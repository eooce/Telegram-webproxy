#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import asyncio
import base64
import hashlib
import hmac
import json
import math
import os
import re
import secrets
import signal
import struct
import subprocess
import sys
import time
from collections import deque, namedtuple

from aiohttp import ClientSession, ClientTimeout, WSMsgType, hdrs, web
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes

# UUID 辅助函数
UUID_RE = re.compile(r'^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$')

def normalize_secret(v):
    s = str(v or '').strip().lower()
    if UUID_RE.match(s):
        return s.replace('-', '')
    return s
    
# ==================== 环境变量 ====================
# SECRET 支持两种写法 422decd7-cc2a-4b86-8a91-c341ecc92045 和 422decd7cc2a4b868a91c341ecc92045 都支持：32 位 hex 或标准 UUID
SECRET = normalize_secret(os.environ.get('UUID') or os.environ.get('SECRET') or 'f9f61360-695b-4f0a-b3e1-41c5c96c28f7')
DOMAIN = (os.environ.get('DOMAIN') or 'webproxy.xxx.com').strip() # Origin Rules 回源后的域名或容器分配的域名，不带 https:// 前缀
PORT = int(os.environ.get('SERVER_PORT') or os.environ.get('PORT') or '3000') # 监听端口，回源时需要

# ==================== 配置 ====================
CFG_DN_PACK = 32 * 1024      # dnPack: 下行合并包上限
CFG_UP_PACK = 20 * 1024      # upPack: 上行合并包上限
CFG_DN_MS = 1                # dnMs: 下行合并等待毫秒
NIL = b''
BAD_HEAD = (b'HEAD', b'POST', b'GET ', b'OPTI')
IS_TYPE = (1, 2, 3, 4, 17)
# Node ws 库默认 maxPayload 为 100MiB，保持一致
WS_MAX_MSG = 100 * 1024 * 1024

Frame = namedtuple('Frame', 'type sid payload')


class Err(Exception):
    """对应 JS 的 Error，message 与原版保持一致。"""


HTTP = None        # 全局 aiohttp ClientSession（拨号 telegram / 查公网 IP）
CFG_CACHE = None   # mk_cfg() 缓存
leases = {}        # session token -> Lease


# ==================== 工具函数 ====================
def b64(v):
    """base64url 无填充（等价 Buffer.toString('base64url')）。"""
    return base64.urlsafe_b64encode(bytes(v)).rstrip(b'=').decode('ascii')


def un64(v):
    s = str(v).replace('-', '+').replace('_', '/')
    s += '=' * ((4 - len(s) % 4) % 4)
    return base64.b64decode(s)


def rand(n):
    return secrets.token_bytes(n)


# ==================== 帧编码/解析 ====================
def enc(typ, sid, data=NIL):
    body = bytes(data)
    if typ not in IS_TYPE:
        raise Err('Invalid type')
    if not isinstance(sid, int) or isinstance(sid, bool) or sid < 0 or sid > 0xffffff:
        raise Err('Invalid sid')
    if len(body) > 1024 * 1024:
        raise Err('Body too large')
    return (bytes([typ, (sid >> 16) & 0xff, (sid >> 8) & 0xff, sid & 0xff])
            + len(body).to_bytes(4, 'big') + body)


def get_frame(b, o):
    if len(b) - o < 8:
        return None, 0
    typ = b[o]
    if typ not in IS_TYPE:
        raise Err('Invalid frame type')
    sid = (b[o + 1] << 16) | (b[o + 2] << 8) | b[o + 3]
    n = int.from_bytes(b[o + 4:o + 8], 'big')
    if n > 1024 * 1024:
        raise Err('Frame too large')
    total = 8 + n
    if len(b) - o < total:
        return None, 0
    return Frame(typ, sid, bytes(b[o + 8:o + total])), total


def frames(v):
    src = bytes(v)
    out = []
    o = 0
    while o < len(src):
        part, consumed = get_frame(src, o)
        if part is None:
            raise Err('Incomplete frame')
        if len(out) >= 4096:
            raise Err('Too many frames')
        out.append(part)
        o += consumed
    return out


def win_of(data):
    if len(data) != 4:
        raise Err('Invalid window')
    n = int.from_bytes(data, 'big')
    if not n:
        raise Err('Zero window')
    return n


def check(fr):
    if fr.type in (1, 3):
        if len(fr.payload):
            raise Err('Empty expected')
        return 0
    if fr.type == 2:
        if not fr.payload:
            raise Err('Non-empty expected')
        return 0
    if fr.type == 4:
        return win_of(fr.payload)
    raise Err('Invalid type')


# ==================== 头部处理 ====================
def head_of(head):
    head = bytes(head)
    tag = struct.unpack('<I', head[56:60])[0]
    mode = 0xef if tag == 0xefefefef else 0xee if tag == 0xeeeeeeee else \
        0xdd if tag == 0xdddddddd else 0
    if not mode:
        raise Err('Invalid mode')
    dc = struct.unpack('<h', head[60:62])[0]
    target = abs(dc) - 1
    if target < 0 or target >= 5:
        raise Err('Invalid DC')
    return mode, target, dc < 0


def mk_head(mode, target, media):
    """生成 64 字节头部（约束与原版相同）。"""
    while True:
        head = bytearray(secrets.token_bytes(64))
        if head[0] == 0xef:
            continue
        if bytes(head[0:4]) in BAD_HEAD:
            continue
        if not any(head[4:8]):
            continue
        break
    head[56:60] = bytes([mode]) * 4
    struct.pack_into('<h', head, 60, (target + 1) * (-1 if media else 1))
    return bytes(head)


# ==================== 密钥/主机 ====================
KEY_RE = re.compile(r'^(?:[0-9a-f]{32}|(?:dd|ee|ef)[0-9a-f]{32})$')


def get_key(v, keep_tag=False):
    s = str(v or '').strip().lower()
    if not KEY_RE.match(s):
        raise Err('Invalid key')
    return bytes.fromhex(s if (keep_tag and len(s) == 34 and s.startswith('dd')) else s[-32:])


LABEL_RE = re.compile(r'^[a-z0-9](?:[a-z0-9-]{0,61}[a-z0-9])?$')


def host_of(v):
    host = str(v or '').strip().lower()
    if host.endswith('.'):
        host = host[:-1]
    labels = host.split('.')
    if ('.' not in host or len(host) > 253 or ':' in host
            or any(not LABEL_RE.match(l) for l in labels)):
        raise Err('Invalid host')
    return host


def derive_boot(secret_raw):
    """从 SECRET 用带标签的 HMAC-SHA256 确定性派生（64 位 hex）。
    修改标签会强制所有已签发 token 失效。"""
    master = hmac.new(b'tg-webproxy-master-v1',
                      str(secret_raw).strip().lower().encode('utf-8'),
                      hashlib.sha256).digest()
    return hmac.new(b'tg-webproxy-boot-v1', master, hashlib.sha256).hexdigest()


# ==================== HMAC / MAC ====================
def mac(boot, kind, body):
    msg = (kind + '\n').encode('utf-8') + bytes(body)
    return hmac.new(boot.encode('utf-8'), msg, hashlib.sha256).digest()[:16]


def mk_token(boot, kind, exp_at, nonce):
    body = bytearray(16)
    struct.pack_into('>I', body, 0, math.ceil(exp_at / 1000))
    body[4:16] = bytes(nonce)[:12]
    token = bytearray(32)
    token[0:16] = body
    token[16:32] = mac(boot, kind, bytes(body))
    return b64(bytes(token))


def mk_boot(boot):
    return mk_token(boot, 'bootstrap', int(time.time() * 1000) + 2 * 60 * 1000, rand(12))


def mk_sess(boot):
    return mk_token(boot, 'session', int(time.time() * 1000) + 5 * 60 * 1000, rand(12))


def verify(v, boot, kind):
    if not isinstance(v, str) or not re.fullmatch(r'[A-Za-z0-9_-]{43}', v):
        return False
    try:
        token = un64(v)
    except Exception:
        return False
    if len(token) != 32 or b64(token) != v:
        return False
    body, sig = token[:16], token[16:]
    exp = int.from_bytes(body[:4], 'big')
    if exp <= int(time.time()):
        return False
    want = mac(boot, kind, body)
    return hmac.compare_digest(sig, want)


def auth_boot(v, boot):
    return v == boot or verify(v, boot, 'bootstrap')


class Lease:
    __slots__ = ('expires', 'active', 'used', 'deleted')

    def __init__(self, expires):
        self.expires = expires
        self.active = set()
        self.used = set()
        self.deleted = False


def mk_lease(token):
    return Lease(int.from_bytes(un64(token)[:4], 'big') * 1000)


def bearer(v):
    m = re.match(r'^Bearer ([^\s]+)$', v or '')
    return m.group(1) if m else None


def is_binary(request):
    return (request.headers.get('Content-Type') or '').strip().lower() == 'application/octet-stream'


def hello(body):
    if (len(body) != 9 or body[0] != 0x10 or body[1] != 0 or body[2] != 0 or body[3] != 0
            or int.from_bytes(body[4:8], 'big') != 1 or body[8] != 1):
        raise Err('Invalid hello')


def protos(request):
    raw = request.headers.get('Sec-WebSocket-Protocol') or ''
    return [p.strip() for p in raw.split(',') if p.strip()]


# ==================== 配置（启动时构造一次） ====================
class Cfg:
    __slots__ = ('secret', 'key', 'boot')

    def __init__(self, secret, key, boot):
        self.secret = secret
        self.key = key
        self.boot = boot


def mk_cfg():
    global CFG_CACHE
    if CFG_CACHE is not None:
        return CFG_CACHE
    secret = str(SECRET or '').strip()
    if not secret:
        raise Err('SECRET required')
    CFG_CACHE = Cfg(secret, get_key(secret), derive_boot(secret))
    return CFG_CACHE


# ==================== Bridge ====================
def mk_cap(secret, host):
    key = get_key(secret, True)
    sig = hmac.new(key, f'tdesktop-web-proxy-bridge-v1\n{host_of(host)}'.encode('utf-8'),
                   hashlib.sha256).digest()
    return b64(sig)


def bridge(request, secret):
    raw_path = request.raw_path
    search = ('?' + raw_path.split('?', 1)[1]) if '?' in raw_path else ''
    if request.path != '/' or len(search) != 51:
        return None
    cand = search[8:]
    if search != '?bridge=' + cand or not re.fullmatch(r'[A-Za-z0-9_-]{43}', cand):
        return None
    host = host_of(request.url.host or '')
    want = mk_cap(secret, host)
    if len(cand) != len(want):
        return None
    diff = 0
    for a, b in zip(cand.encode('ascii'), want.encode('ascii')):
        diff |= a ^ b
    return host if diff == 0 else None


# ==================== 加密 ====================
_CTR_MAX = (1 << 128) - 1


def sha256(v):
    return hashlib.sha256(bytes(v)).digest()


def step(ctr, n):
    """计数器前进 n 个块（大端 128 位加法，溢出报错）。"""
    v = int.from_bytes(ctr, 'big') + n
    if v > _CTR_MAX:
        raise Err('Counter overflow')
    return v.to_bytes(16, 'big')


class AesCtr:
    """与 JS mkCtr() 相同语义的 AES-128/256-CTR（维护跨块 tail 状态）。"""

    def __init__(self, key, ctr):
        self.key = bytes(key)
        self.iv = bytes(ctr)
        self.tail = NIL

    def _encrypt(self, iv, data):
        if not data:
            return NIL
        encr = Cipher(algorithms.AES(self.key), modes.CTR(iv)).encryptor()
        return encr.update(data) + encr.finalize()

    def crypt(self, v):
        b = bytes(v)
        if not b:
            return NIL
        if not self.tail and len(b) % 16 == 0:
            raw = self._encrypt(self.iv, b)
            self.iv = step(self.iv, len(b) // 16)
            return raw
        if len(b) <= len(self.tail):
            out = bytes(x ^ y for x, y in zip(b, self.tail))
            self.tail = self.tail[len(b):]
            return out
        skip = 16 - len(self.tail) if self.tail else 0
        ctr = self.iv
        if skip:
            ctr = ((int.from_bytes(self.iv, 'big') - 1) & _CTR_MAX).to_bytes(16, 'big')
        end = skip + len(b)
        block = bytearray((end + 15) // 16 * 16)
        block[skip:skip + len(b)] = b
        raw = self._encrypt(ctr, bytes(block))
        self.tail = raw[end:]
        self.iv = step(self.iv, len(block) // 16 - (1 if skip else 0))
        return bytes(raw[skip:end])


def make_cipher(head, secret, reverse):
    mat = bytearray(bytes(head)[8:56])
    if reverse:
        mat.reverse()
    key = sha256(bytes(mat[:32]) + bytes(secret)) if len(secret) else bytes(mat[:32])
    return AesCtr(key, bytes(mat[32:48]))


def wire_head(head):
    """生成发往 telegram 的 64 字节线头（前 56 字节明文）。"""
    ctr = make_cipher(head, NIL, False)
    raw = bytearray(ctr.crypt(head))
    raw[0:56] = head[0:56]
    return bytes(raw), ctr


# ==================== 数据包解析 ====================
class PktParser:
    """与 JS mkPkt() 相同：按 mode 解析上行组包。"""

    def __init__(self, mode):
        self.mode = mode
        self.tail = NIL

    def push(self, v):
        b = bytes(v)
        if b:
            self.tail = self.tail + b if self.tail else b
        pkts = []
        tail = self.tail
        o = 0
        while True:
            avail = len(tail) - o
            if self.mode == 0xef:
                if avail < 1:
                    break
                words = tail[o] & 0x7f
                if words == 0x7f:
                    if avail < 4:
                        break
                    words = tail[o + 1] | (tail[o + 2] << 8) | (tail[o + 3] << 16)
                    h_len = 4
                else:
                    h_len = 1
                p_len = words * 4
            else:
                if avail < 4:
                    break
                p_len = int.from_bytes(tail[o:o + 4], 'little') & 0x7fffffff
                h_len = 4
            if not p_len or p_len > 8 * 1024 * 1024:
                raise Err('Invalid packet length')
            total = h_len + p_len
            if avail < total:
                break
            pkts.append(bytes(tail[o:o + total]))
            o += total
        if o:
            self.tail = NIL if o == len(tail) else tail[o:]
        if len(self.tail) > 8 * 1024 * 1024 + 4:
            raise Err('Tail overflow')
        return pkts

    def clear(self):
        self.tail = NIL


def spawn(coro):
    """创建后台任务并吞掉异常，避免 asyncio 未捕获警告。"""
    try:
        loop = asyncio.get_running_loop()
    except RuntimeError:
        return None
    task = loop.create_task(coro)
    task.add_done_callback(_swallow)
    return task


def _swallow(task):
    if not task.cancelled():
        try:
            task.exception()
        except Exception:
            pass


# ==================== Wire (WebSocket -> telegram) ====================
def hosts(dc, media):
    return [f'kws{dc}{"-1" if media else ""}.web.telegram.org',
            f'kws{dc}{"" if media else "-1"}.web.telegram.org']


async def _close_ws_quiet(ws):
    try:
        await ws.close(code=1000)
    except Exception:
        pass


class Wire:
    """与 JS mkWire() 相同：带下行合并(32KB/1ms)的 WS 收发器。"""

    def __init__(self, ws):
        self.ws = ws
        self.q = []
        self.h = 0
        self.q_bytes = 0
        self.waiters = []
        self.closed = False   # 连接已结束（对应 JS closed）
        self.dead = False     # 本地 close 已调用（对应 JS dead）
        self.fault = None
        self.ready = asyncio.get_running_loop().create_future()
        self.ready.set_result(self)
        self._p_event = None
        self._p_need = 0
        self._reader = spawn(self._read())

    async def _read(self):
        err = None
        try:
            async for msg in self.ws:
                t = msg.type
                if t == WSMsgType.BINARY:
                    if msg.data:
                        self._on_msg(bytes(msg.data))
                elif t == WSMsgType.TEXT:
                    data = msg.data.encode('utf-8')
                    if data:
                        self._on_msg(data)
                elif t == WSMsgType.ERROR:
                    err = Err('WS error')
                    break
                else:
                    break   # CLOSE / CLOSING / CLOSED
        except Exception:
            err = Err('WS error')
        if err is None:
            code = self.ws.close_code
            if code and code != 1000:
                err = Err(f'Closed {code}')
        self._end(err)

    def _on_msg(self, b):
        if self.closed:
            return
        if self.waiters:
            fut = self.waiters.pop(0)
            if not fut.done():
                fut.set_result(b)
            return
        self.q.append(b)
        self.q_bytes += len(b)
        ev = self._p_event
        if ev is not None and (self.q_bytes >= self._p_need or len(b) >= CFG_DN_PACK):
            ev.set()

    def _end(self, err=None):
        if self.closed:
            return
        self.closed = True
        self.fault = err
        ev = self._p_event
        if ev is not None:
            ev.set()
        waiters = self.waiters
        self.waiters = []
        for fut in waiters:
            if fut.done():
                continue
            if err is not None:
                fut.set_exception(err)
            else:
                fut.set_result(None)

    async def write(self, v):
        await self.ready
        if self.closed:
            raise self.fault if self.fault is not None else Err('Closed')
        await self.ws.send_bytes(bytes(v))

    async def take(self):
        if self.h < len(self.q):
            msg = self.q[self.h]
            self.q[self.h] = None
            self.h += 1
            self.q_bytes -= len(msg)
            self._trim()
            return msg
        if self.fault is not None:
            raise self.fault
        if self.closed:
            return None
        fut = asyncio.get_running_loop().create_future()
        self.waiters.append(fut)
        return await fut

    async def read_pack(self):
        first = await self.take()
        if self.dead:
            return None
        if first is None or len(first) >= CFG_DN_PACK:
            return first
        if not self.closed and self.q_bytes < CFG_DN_PACK - len(first):
            ev = asyncio.Event()
            self._p_event = ev
            self._p_need = CFG_DN_PACK - len(first)
            try:
                await asyncio.wait_for(ev.wait(), CFG_DN_MS / 1000)
            except (asyncio.TimeoutError, TimeoutError):
                pass
            finally:
                if self._p_event is ev:
                    self._p_event = None
        if self.dead:
            return None
        n = len(first)
        end = self.h
        while end < len(self.q) and n + len(self.q[end]) <= CFG_DN_PACK:
            n += len(self.q[end])
            end += 1
        if end == self.h:
            return first
        parts = [first]
        while self.h < end:
            part = self.q[self.h]
            self.q[self.h] = None
            self.h += 1
            self.q_bytes -= len(part)
            parts.append(part)
        self._trim()
        return b''.join(parts)

    def _trim(self):
        if self.h == len(self.q):
            self.q.clear()
            self.h = 0
        elif self.h >= 256 and self.h * 2 >= len(self.q):
            del self.q[:self.h]
            self.h = 0

    def close(self):
        if self.dead:
            return
        self.dead = True
        if not self.closed:
            self._end(None)
        self.q.clear()
        self.h = 0
        self.q_bytes = 0
        try:
            asyncio.get_running_loop().create_task(_close_ws_quiet(self.ws))
        except RuntimeError:
            pass


async def dial(target, media, aborted):
    """对应 JS dial()：逐个候选 DC 拨号，7.5s 超时，支持 abort。"""
    for host in hosts(target + 1, media):
        if aborted.is_set():
            raise Err('Aborted')
        url = f'wss://{host}/apiws'
        conn = asyncio.ensure_future(
            HTTP.ws_connect(url, protocols=('binary',), max_msg_size=WS_MAX_MSG))
        waiter = asyncio.ensure_future(aborted.wait())
        done, pending = await asyncio.wait(
            {conn, waiter}, timeout=7.5, return_when=asyncio.FIRST_COMPLETED)
        for t in pending:
            t.cancel()
        if pending:
            await asyncio.gather(*pending, return_exceptions=True)
        if waiter in done:
            if conn.done() and not conn.cancelled() and not conn.exception():
                await _close_ws_quiet(conn.result())
            raise Err('Aborted')
        if conn not in done:   # 打开超时
            continue
        if conn.exception() is not None:
            if aborted.is_set():
                raise Err('Aborted')
            continue
        wire = Wire(conn.result())
        if aborted.is_set():
            wire.close()
            raise Err('Aborted')
        return wire
    if aborted.is_set():
        raise Err('Aborted')
    raise Err('All DCs failed')


# ==================== 流管理 ====================
class _Job:
    __slots__ = ('data', 'consumed', 'result')

    def __init__(self, data):
        self.data = data
        self.consumed = False
        self.result = None


class ProxyStream:
    """对应 JS mkStream()：64 字节头 -> 拨号 -> 加密泵送。"""

    def __init__(self, secret, emit, on_close):
        self.secret = secret
        self.emit = emit          # async def emit(bytes)
        self.on_close = on_close  # 同步回调
        self.hdr = NIL
        self.c_in = None
        self.c_out = None
        self.k_in = None
        self.k_out = None
        self.peer = None
        self.pkt = None
        self.init = False
        self.closed = False
        self.chain = asyncio.Lock()
        self.uq = deque()
        self.aborted = asyncio.Event()
        self.pump_task = None

    async def push(self, v):
        if self.closed:
            raise Err('Closed')
        job = _Job(bytes(v))
        self.uq.append(job)
        async with self.chain:
            if self.closed:
                raise Err('Closed')
            if job.consumed:
                return job.result
            jobs = [job]
            n = len(job.data)
            for nxt in self.uq:
                if nxt is job:
                    continue
                if n >= CFG_UP_PACK or n + len(nxt.data) > CFG_UP_PACK:
                    break
                n += len(nxt.data)
                jobs.append(nxt)
            data = job.data if len(jobs) == 1 else b''.join(j.data for j in jobs)
            for item in jobs:
                try:
                    self.uq.remove(item)
                except ValueError:
                    pass
                item.consumed = True
                item.data = None
            out = await self.feed(data)
            for item in jobs:
                item.result = out
            return out

    async def feed(self, b):
        if self.closed:
            raise Err('Closed')
        if self.init and self.peer.closed:
            return False
        if not b:
            return None
        if not self.init:
            need = 64 - len(self.hdr)
            if len(b) < need:
                self.hdr += b
                return None
            self.hdr += b[:need]
            await self.start()
            rest = b[need:]
            if rest:
                return await self.write(rest)
            return None
        return await self.write(b)


    async def start(self):
        raw = self.hdr
        cr = make_cipher(raw, self.secret, False)
        plain = cr.crypt(raw)
        if self.closed:
            return
        mode, target, media = head_of(plain)
        head = mk_head(mode, target, media)
        cw = make_cipher(raw, self.secret, True)
        wire_bytes, k_out = wire_head(head)
        kr = make_cipher(head, NIL, True)
        if self.closed:
            return
        kws = await dial(target, media, self.aborted)
        if self.closed:
            kws.close()
            return
        self.peer = kws
        self.c_in = cr
        self.c_out = cw
        self.k_out = k_out
        self.k_in = kr
        self.pkt = PktParser(mode)
        await kws.write(wire_bytes)
        if self.closed:
            return
        self.hdr = NIL
        self.init = True
        self.pump_task = spawn(self._pump())

    async def write(self, raw):
        if self.closed or self.peer.closed:
            return False
        plain = self.c_in.crypt(raw)
        if self.closed or self.peer.closed:
            return False
        pkts = self.pkt.push(plain)
        start = 0
        while start < len(pkts):
            end = start + 1
            n = len(pkts[start])
            while end < len(pkts) and n + len(pkts[end]) <= CFG_UP_PACK:
                n += len(pkts[end])
                end += 1
            chunk = pkts[start] if end == start + 1 else b''.join(pkts[start:end])
            if self.closed or self.peer.closed:
                return False
            wire = self.k_out.crypt(chunk)
            o = 0
            while start < end:
                if self.closed or self.peer.closed:
                    return False
                sz = len(pkts[start])
                try:
                    await self.peer.write(wire[o:o + sz])
                except Exception:
                    if self.closed or self.peer.closed:
                        return False
                    raise
                o += sz
                start += 1
        return None

    async def _pump(self):
        try:
            while not self.closed:
                b = await self.peer.read_pack()
                if self.closed:
                    return
                if not b:
                    self.close()
                    return
                plain = self.k_in.crypt(b)
                if self.closed:
                    return
                raw = self.c_out.crypt(plain)
                if self.closed:
                    return
                await self.emit(raw)
        except Exception:
            pass
        finally:
            self.close()

    def close(self):
        if self.closed:
            return
        self.closed = True
        self.aborted.set()
        if self.peer is not None:
            self.peer.close()
        self.uq.clear()
        self.hdr = NIL
        if self.pkt is not None:
            self.pkt.clear()
        self.c_in = self.c_out = self.k_in = self.k_out = None
        self.peer = None
        cb = self.on_close
        if cb is not None:
            try:
                cb()
            except Exception:
                pass


# ==================== 会话管理 ====================
class StreamState:
    __slots__ = ('win_in', 'win_out', 'ev', 'closed', 'p_items', 'proxy')

    def __init__(self):
        self.win_in = 4 * 1024 * 1024
        self.win_out = 4 * 1024 * 1024
        self.ev = asyncio.Event()
        self.closed = False
        self.p_items = 0
        self.proxy = None


class Session:
    """对应 JS mkSession()。"""

    def __init__(self, secret, sid, on_close, lease=None):
        self.secret = secret
        self.sid = sid
        self.lease = lease
        self.on_close = on_close
        self.sock = None
        self.closed = False
        self.tx = asyncio.Lock()
        self.cur = None
        self.reader_task = None
        self._close_evt = asyncio.Event()
        self._close_info = (1000, '')

    async def wait_closed(self):
        """阻塞直到会话关闭：保持 handler 存活，避免 aiohttp 提前 write_eof 关闭连接。"""
        await self._close_evt.wait()
        sock = self.sock
        if sock is not None:
            await self._close_sock(sock, *self._close_info)

    # ---- 连接 ----
    def attach(self, ws):
        if self.sock is not None or self.closed:
            raise Err('Already attached')
        self.sock = ws
        self.reader_task = spawn(self._reader())

    async def _reader(self):
        try:
            async for msg in self.sock:
                if self.closed:
                    continue
                if msg.type == WSMsgType.BINARY:
                    data = msg.data
                elif msg.type == WSMsgType.TEXT:
                    data = msg.data.encode('utf-8')
                else:
                    break   # ERROR / CLOSED / ...
                if self.closed:
                    continue
                try:
                    await self._on_data(bytes(data))
                except Exception:
                    self.close(1008)
                    break
        except Exception:
            pass
        finally:
            self.close()

    async def _on_data(self, b):
        if self.closed:
            return
        if self.lease is not None and self.lease.deleted:
            self.close(1000)
            return
        if not b or len(b) > 2 * 1024 * 1024:
            raise Err('Bad data')
        for fr in frames(b):
            if self.closed:
                return
            delta = check(fr)
            if fr.sid != self.sid:
                raise Err('SID mismatch')
            if self.cur is None and fr.type != 1:
                raise Err('No stream')
            if fr.type != 1 and self.cur is not None and self.cur.closed:
                continue
            if fr.type == 1:
                self._open()
            elif fr.type == 2:
                await self._write_frame(fr.payload)
            elif fr.type == 4:
                self._grant(delta)
            elif fr.type == 3:
                await self._end(False)
            else:
                raise Err('Bad type')

    async def _send(self, typ, data=NIL):
        out = enc(typ, self.sid, data)
        st = self.cur if typ in (2, 4) else None
        async with self.tx:
            if self.closed:
                raise Err('Closed')
            if typ in (2, 4) and (st is None or st.closed):
                return
            await self.sock.send_bytes(out)

    def _open(self):
        if self.closed:
            return
        if self.cur is not None:
            raise Err('Already open')
        st = StreamState()
        st.proxy = ProxyStream(
            self.secret,
            emit=lambda b: self._emit_dn(st, b),
            on_close=lambda: self._stream_closed(st),
        )
        self.cur = st

    def _stream_closed(self, st):
        if self.closed or st.closed:
            return
        spawn(self._end(True))


    async def _write_frame(self, data):
        if self.closed or (self.cur is not None and self.cur.closed):
            return
        st = self.cur
        if st is None or st.closed:
            raise Err('No stream')
        n = len(data)
        if n > st.win_in:
            raise Err('Window exceeded')
        if st.p_items >= 16384:
            raise Err('Too many items')
        st.win_in -= n
        st.p_items += 1
        try:
            accepted = await st.proxy.push(data)
        except Exception:
            self._free_up(st)
            if not self.closed and not st.closed:
                st.proxy.close()
            return
        self._free_up(st)
        if self.closed or st.closed or accepted is False:
            return
        st.win_in += n
        try:
            await self._send(4, n.to_bytes(4, 'big'))
        except Exception:
            self.close()

    def _free_up(self, st):
        if st.closed:
            return
        st.p_items -= 1

    async def _emit_dn(self, st, b):
        o = 0
        total = len(b)
        while o < total:
            while True:
                st.ev.clear()
                if self.closed or st.closed:
                    raise Err('Closed')
                if st.win_out > 0:
                    break
                await st.ev.wait()
            n = min(64 * 1024, total - o, st.win_out)
            st.win_out -= n
            await self._send(2, b[o:o + n])
            o += n

    def _grant(self, n):
        if self.closed or (self.cur is not None and self.cur.closed):
            return
        st = self.cur
        if st is None or st.closed:
            raise Err('No stream')
        st.win_out = min(0xffffffff, st.win_out + n)
        st.ev.set()

    def _stop(self, st):
        st.closed = True
        st.p_items = 0
        st.ev.set()
        st.proxy.close()

    async def _end(self, notify):
        if self.closed or (self.cur is not None and self.cur.closed):
            return
        st = self.cur
        if st is None:
            raise Err('No stream')
        self._stop(st)
        if notify:
            try:
                await self._send(3)
            except Exception:
                pass
            self.close()
        else:
            self.close()

    def close(self, code=1000, reason=''):
        if self.closed:
            return
        self.closed = True
        if self.cur is not None:
            self._stop(self.cur)
        self.cur = None
        self._close_info = (code, reason)
        sock = self.sock
        if sock is not None:
            spawn(self._close_sock(sock, code, reason))
        cb = self.on_close
        self.on_close = None
        if cb is not None:
            try:
                cb()
            except Exception:
                pass
        self._close_evt.set()

    @staticmethod
    async def _close_sock(sock, code, reason):
        try:
            await sock.close(code=code, message=(reason or '').encode())
        except Exception:
            pass


# ==================== 页面生成 ====================
PAGE_TEMPLATE = r'''<script nonce="__NONCE__">
(()=>{'use strict'; const origin=__ORIGIN__,boot=__BOOTSTRAP__;
const aNonce=/^#android=([A-Za-z0-9_-]{43})$/.exec(location.hash)?.[1]??''; history.replaceState(null,'',location.pathname);
let init=false,closed=false,port=null,token='',started=false,delSent=false; let qBytes=0,qItems=0;
const lanes=new Map(),used=new Set(),qMax=33554432,iMax=16384,msgMax=2097152; const laneMax=8388608,laneItems=1024;
const state=st=>port&&!closed&&port.postMessage({t:'status',state:st});
const opts=(method,token,body,keepalive)=>({ method,body,keepalive:!!keepalive,mode:'same-origin',credentials:'omit',cache:'no-store',redirect:'error',referrerPolicy:'no-referrer', headers:{...(token&&{Authorization:'Bearer '+token}),...(body&&{'Content-Type':'application/octet-stream'})} });
function check(v){ if(!(v instanceof ArrayBuffer)||!v.byteLength||v.byteLength>msgMax)throw Error(); const view=new DataView(v);let o=0,frames=0; while(o<v.byteLength){ if(v.byteLength-o<8||frames++>=4096)throw Error(); const type=view.getUint8(o),n=view.getUint32(o+4),end=o+8+n; if(n>1048576||end>v.byteLength||(type===2&&!n))throw Error(); o=end; } return v; }
function split(v){ check(v);const view=new DataView(v),out=[];let o=0; while(o<v.byteLength){ const end=o+8+view.getUint32(o+4); out.push(o===0&&end===v.byteLength?v:v.slice(o,end));o=end; } return out; }
function sid(v){const b=new Uint8Array(v);return (b[1]<<16)|(b[2]<<8)|b[3];}
function hold(lane,v){ let buffered=0;for(const {ws} of lanes.values())buffered+=ws?.bufferedAmount??0; const own=lane.ws?.bufferedAmount??0; if(qBytes+buffered>qMax-v.byteLength||qItems>=iMax ||lane.bytes+own>laneMax-v.byteLength||lane.items>=laneItems)return false; qBytes+=v.byteLength;qItems++;lane.bytes+=v.byteLength;lane.items++;return true; }
function free(lane,v){qBytes-=v.byteLength;qItems--;lane.bytes-=v.byteLength;lane.items--;}
function fail(){ if(closed)return;state('failed');port?.postMessage({t:'close'});close(true); }
function drop(){ if(delSent||!token)return;delSent=true; fetch(origin+'/api/v1/session',opts('DELETE',token,null,true)).catch(()=>{}); }
function pump(lane){ const ws=lane.ws; if(closed||lane.done||!ws||ws.readyState!==WebSocket.OPEN||!lane.pending.length)return; if(ws.bufferedAmount>=msgMax){lane.timer ||= setTimeout(()=>{lane.timer=0;pump(lane);},10);return;} try{ const v=lane.pending.shift();ws.send(v);free(lane,v); port.postMessage({t:'traffic',up:v.byteLength,down:0}); if(lane.pending.length)queueMicrotask(()=>pump(lane)); }catch{fail();} }
function push(v){ try{for(const frame of split(v))pushLane(frame);} catch{fail();} }
function end(lane,notify){ if(lane.done)return;lane.done=true;if(lane.timer)clearTimeout(lane.timer); qBytes-=lane.bytes;qItems-=lane.items;lane.bytes=lane.items=0;lane.pending.length=0;lanes.delete(lane.id); try{lane.ws?.close();}catch{} if(notify&&port&&!closed){const frame=new ArrayBuffer(8),b=new Uint8Array(frame);b[0]=3;b[1]=lane.id>>>16;b[2]=lane.id>>>8;b[3]=lane.id;port.postMessage(frame,[frame]);} }
function open(lane){ const target=origin.replace(/^https:/,'wss:')+'/api/v1/ws'; const ws=lane.ws=new WebSocket(target,'tproxy-lane-v1.'+token+'.'+lane.id);ws.binaryType='arraybuffer'; ws.onopen=()=>{if(closed||lane.done){ws.close();return;}lane.opened=true;state('connected');pump(lane);}; ws.onmessage=e=>{ if(closed||lane.done)return; try{ const frames=split(e.data); if(frames.some(frame=>sid(frame)!==lane.id))throw Error(); const ended=frames.some(frame=>new Uint8Array(frame)[0]===3); if(ended)lane.rClosed=true; port.postMessage({t:'traffic',up:0,down:e.data.byteLength});port.postMessage(e.data,[e.data]);state('connected'); if(ended)end(lane,false); }catch{fail();} }; ws.onerror=()=>{}; ws.onclose=()=>{if(closed||lane.done)return;if(!lane.opened){fail();return;}end(lane,!lane.lClosed&&!lane.rClosed);}; }
function pushLane(v){ const id=sid(v),type=new Uint8Array(v)[0];let lane=lanes.get(id); if(!id)throw Error(); if(!lane&&(type===2||type===3||type===4))return; if(!lane){ if(type!==1||used.has(id)||lanes.size>=128||used.size>=4096)throw Error(); used.add(id);lane={id,ws:null,pending:[],bytes:0,items:0,timer:0,opened:false,done:false,lClosed:false,rClosed:false};lanes.set(id,lane); } if(lane.lClosed)return; if(type===3&&!lane.opened){end(lane,false);return;} if(!hold(lane,v))throw Error(); lane.pending.push(v);if(type===3)lane.lClosed=true; if(token){if(!lane.ws)open(lane);else pump(lane);} }
async function create(first){ try{ state('connecting'); const res=await fetch(origin+'/api/v1/session',opts('POST',boot,first)); if(res.status!==200||res.headers.get('X-Carrier-Mode')!=='websocket-lanes')throw Error(); token=res.headers.get('X-Session-Token')??''; if(!token)throw Error(); const welcome=await res.arrayBuffer();check(welcome); if(closed){drop();return;} port.postMessage(welcome,[welcome]);state('connected'); for(const lane of lanes.values())if(!lane.ws)open(lane); }catch{fail();} }
function close(notify){ if(closed)return;closed=true; for(const lane of [...lanes.values()])end(lane,false);used.clear(); if(notify)drop(); port?.close(); }
function start(next){ init=true;port=next; port.onmessage=msg=>{ const data=msg.data; if(data instanceof ArrayBuffer){ if(!started){ try{check(data);}catch{fail();return;} started=true;create(data); }else push(data); }else if(data&&data.t==='close')close(true); }; port.start();state('connecting'); }
addEventListener('message',e=>{ if(init||e.source!==parent||e.data===null||typeof e.data!=='object')return; const keys=Object.keys(e.data).sort(); if(keys.length!==2||keys[0]!=='t'||keys[1]!=='v'||e.data.t!=='tproxy-init'||e.data.v!==1||e.ports.length!==1)return; let src;try{src=new URL(e.origin);}catch{return;} if(src.protocol!=='http:'||src.hostname!=='127.0.0.1'||!src.port||src.origin!==e.origin)return; start(e.ports[0]); }); const android=globalThis.TelegramWebProxy;
if(!init&&aNonce&&android&&typeof android.postMessage==='function'){ const aPort={onmessage:null,start(){},close(){android.onmessage=null;},postMessage(v){ if(v instanceof ArrayBuffer){for(const frame of split(v))android.postMessage(frame);} else android.postMessage(JSON.stringify(v)); }}; android.onmessage=e=>{ let data=e.data;if(typeof data==='string'){try{data=JSON.parse(data);}catch{return;}} aPort.onmessage?.({data}); }; start(aPort);android.postMessage(JSON.stringify({t:'tproxy-android-init',v:1,nonce:aNonce})); } addEventListener('pagehide',()=>close(true),{once:true}); })();
</script>'''

SIMPLE_PAGE = '<!doctype html><meta charset="utf-8"><title>Connection</title>'

PERMISSIONS_POLICY = ', '.join([
    'accelerometer=()', 'autoplay=()', 'camera=()',
    'clipboard-read=()', 'clipboard-write=()', 'display-capture=()',
    'encrypted-media=()', 'fullscreen=()', 'geolocation=()',
    'gyroscope=()', 'hid=()', 'idle-detection=()', 'magnetometer=()',
    'microphone=()', 'midi=()', 'payment=()', 'picture-in-picture=()',
    'publickey-credentials-create=()', 'publickey-credentials-get=()',
    'screen-wake-lock=()', 'serial=()', 'usb=()', 'web-share=()',
    'xr-spatial-tracking=()',
])


def mk_page(host, boot):
    nonce = b64(rand(18))
    body = (PAGE_TEMPLATE
            .replace('__NONCE__', nonce)
            .replace('__ORIGIN__', json.dumps(f'https://{host}'))
            .replace('__BOOTSTRAP__', json.dumps(str(boot))))
    csp = '; '.join([
        "default-src 'none'", "base-uri 'none'", "child-src 'none'",
        f"connect-src 'self' wss://{host}", "font-src 'none'", "form-action 'none'",
        'frame-ancestors http://127.0.0.1:*', "frame-src 'none'", "img-src 'none'",
        "manifest-src 'none'", "media-src 'none'", "object-src 'none'",
        f"script-src 'nonce-{nonce}'", "style-src 'none'", "worker-src 'none'",
        'sandbox allow-same-origin allow-scripts',
    ])
    return body, csp


# ==================== HTTP 路由 ====================
async def route(request):
    path = request.path
    method = request.method

    try:
        cfg = mk_cfg()
    except Exception:
        if path in ('/', '/health', '/api/v1/session', '/api/v1/ws'):
            return web.Response(status=500)
        return web.Response(status=404)

    # 根路径
    if path == '/' and method in ('GET', 'HEAD'):
        host = None
        if method == 'GET':
            try:
                host = bridge(request, cfg.secret)
            except Exception:
                host = None
        if host:
            boot = mk_boot(cfg.boot)
            body, csp = mk_page(host, boot)
            return web.Response(
                status=200,
                body=None if method == 'HEAD' else body.encode('utf-8'),
                headers={
                    'Content-Type': 'text/html; charset=utf-8',
                    'Content-Security-Policy': csp,
                    'Cache-Control': 'no-store',
                    'Referrer-Policy': 'no-referrer',
                    'X-Content-Type-Options': 'nosniff',
                    'Permissions-Policy': PERMISSIONS_POLICY,
                })
        return web.Response(
            status=200,
            body=None if method == 'HEAD' else SIMPLE_PAGE.encode('utf-8'),
            headers={'Content-Type': 'text/html; charset=utf-8'})

    # 健康检查
    if path == '/health':
        return web.Response(status=200, text='{"ok":true}',
                            content_type='application/json', charset='utf-8')

    # 会话 API
    if path == '/api/v1/session':
        auth = bearer(request.headers.get('Authorization'))
        if method == 'DELETE':
            if not auth or not verify(auth, cfg.boot, 'session'):
                return web.Response(status=404)
            lease = leases.get(auth)
            if lease is None:
                lease = mk_lease(auth)
                leases[auth] = lease
            lease.deleted = True
            return web.Response(status=204)
        if method != 'POST' or not auth or not is_binary(request):
            return web.Response(status=404)
        if not auth_boot(auth, cfg.boot):
            return web.Response(status=404)
        try:
            body = await request.read()
            hello(body)
            token = mk_sess(cfg.boot)
            return web.Response(
                status=200, body=enc(0x11, 0),
                headers={
                    'Content-Type': 'application/octet-stream',
                    'Cache-Control': 'no-store',
                    'X-Session-Token': token,
                    'X-Carrier-Mode': 'websocket-lanes',
                })
        except Exception:
            return web.Response(status=404)


    # WebSocket 升级
    origin = request.headers.get('Origin')
    if (path != '/api/v1/ws' or method != 'GET'
            or (request.headers.get('Upgrade') or '').lower() != 'websocket'
            or (origin and origin not in (f'https://{request.host}',
                                         f'http://{request.host}'))):
        return web.Response(status=404)

    offers = protos(request)
    proto = offers[0] if len(offers) == 1 else None
    parts = proto.split('.') if proto is not None else []
    kind = parts[0] if len(parts) > 0 else ''
    token = parts[1] if len(parts) > 1 else ''
    sid_str = parts[2] if len(parts) > 2 else None
    if (len(parts) != 3 or kind != 'tproxy-lane-v1' or sid_str is None
            or not re.fullmatch(r'[1-9][0-9]{0,7}', sid_str) or int(sid_str) > 0xffffff
            or not verify(token, cfg.boot, 'session')):
        return web.Response(status=404)
    sid = int(sid_str)

    now = int(time.time() * 1000)
    for key in list(leases.keys()):
        v = leases[key]
        if v.expires <= now and not v.active:
            del leases[key]
    lease = leases.get(token)
    if lease is None:
        if len(leases) >= 4096:
            return web.Response(status=503)
        lease = mk_lease(token)
        leases[token] = lease
    if (lease.deleted or sid in lease.used or len(lease.active) >= 128
            or len(lease.used) >= 4096):
        return web.Response(status=409)
    lease.used.add(sid)
    lease.active.add(sid)

    sess = Session(secret=cfg.key, sid=sid, lease=lease,
                   on_close=lambda: lease.active.discard(sid))

    ws = web.WebSocketResponse(protocols=(proto,), compress=False,
                               max_msg_size=WS_MAX_MSG,
                               autoping=True, autoclose=True, receive_timeout=None)
    try:
        await ws.prepare(request)
    except Exception:
        sess.close()   # 握手失败：释放 lease.active 并抛出（同 Node 400 行为）
        raise
    try:
        sess.attach(ws)
    except Exception:
        sess.close()
        spawn(_close_ws_quiet(ws))
        return ws
    # 关键：handler 需等待会话结束再返回，否则 aiohttp 会立即 write_eof -> close(1000)
    await sess.wait_closed()
    return ws


async def guarded(request):
    try:
        return await route(request)
    except web.HTTPException:
        raise
    except Exception:
        return web.Response(status=500)


def build_app():
    # Node 版不校验请求体大小：client_max_size=0 表示不限制
    app = web.Application(client_max_size=0)
    app.router.add_route(hdrs.METH_ANY, '/', guarded)
    app.router.add_route(hdrs.METH_ANY, '/{tail:.*}', guarded)
    return app


# ==================== 获取公网 IP（DOMAIN 为空时的回退） ====================
# 与原版一致：HTTP 探测 3s 超时（JS: fetchText(url, 3000) + curl -sm 3）
IP_TIMEOUT = 3


async def _fetch_text(url, timeout=IP_TIMEOUT):
    # 全局会话是 total=None，此处按请求覆盖为有限超时（等价 JS 的 { timeout: 3000 }）
    async with HTTP.get(url, timeout=ClientTimeout(total=timeout)) as resp:
        return (await resp.text()).strip()


def _curl(target):
    out = subprocess.run(['curl', '-sm', str(IP_TIMEOUT), target],
                         capture_output=True, timeout=IP_TIMEOUT + 5, check=True)
    return out.stdout.decode('utf-8', 'replace').strip()


async def get_server_ip():
    # IPv4 (HTTP 探测)
    try:
        return await _fetch_text('https://ipv4.ip.sb')
    except Exception:
        pass
    try:
        return _curl('ipv4.ip.sb')
    except Exception:
        pass
    # IPv6 (需要方括号)
    try:
        return '[' + await _fetch_text('https://ipv6.ip.sb') + ']'
    except Exception:
        pass
    try:
        return '[' + _curl('ipv6.ip.sb') + ']'
    except Exception as err:
        print(f'Failed to get IP address: {err}', file=sys.stderr)
        return ''


# ==================== 服务器启动 ====================
async def main():
    global HTTP
    loop = asyncio.get_running_loop()
    stop = asyncio.Event()

    def on_sigint():
        loop.call_soon_threadsafe(stop.set)

    try:
        signal.signal(signal.SIGINT, on_sigint)
    except (ValueError, OSError):
        pass

    app = build_app()
    runner = web.AppRunner(app, access_log=None)
    await runner.setup()
    site = web.TCPSite(runner, '0.0.0.0', PORT)
    await site.start()
    print(f'TG WebProxy listening on :{PORT}', flush=True)

    HTTP = ClientSession(timeout=ClientTimeout(total=None))

    # 校验 SECRET
    try:
        cfg = mk_cfg()
    except Exception as err:
        print(f'Config error: {err}', file=sys.stderr)
        print('Please set SECRET (32-hex, or dd/ee/ef + 32-hex).', file=sys.stderr)
        await runner.cleanup()
        await HTTP.close()
        sys.exit(1)

    # 决定对外主机名
    host = DOMAIN
    if not host:
        print('DOMAIN is empty, fetching public IP ...', flush=True)
        host = await get_server_ip()
        if not host:
            print('Failed to determine public IP, skip link printing.', file=sys.stderr)
    else:
        try:
            host_of(host)
        except Exception as err:
            print(f'Invalid DOMAIN ({host}): {err}', file=sys.stderr)
            host = None

    # 打印链接
    if host:
        secret_hex = cfg.secret   # canonical wire form (uuid dashes stripped / dd kept)
        print('\n=== Telegram WebProxy Link ===')
        print(f'https://t.me/webproxy?server={host}&secret={secret_hex}')
        print('==============================\n', flush=True)

    await stop.wait()
    print('\nShutting down ...', flush=True)
    try:
        await asyncio.wait_for(runner.cleanup(), 3)
    except (asyncio.TimeoutError, TimeoutError):
        pass
    if HTTP is not None:
        try:
            await HTTP.close()
        except Exception:
            pass


if __name__ == '__main__':
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        print('\nShutting down ...', flush=True)
