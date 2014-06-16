#!/usr/bin/python3
# -*- coding: utf-8 -*-
# Welcome to ⊔net!
#-----------------------------------------------------------------------------
#  © Copyright 2013 ⊔Foundation
#    This file is part of ⊔net.
#
#    ⊔net is free software: you can redistribute it and/or modify
#    it under the terms of the GNU General Public License as published by
#    the Free Software Foundation, either version 3 of the License, or
#    (at your option) any later version.
#
#    ⊔net is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#    GNU General Public License for more details.
#
#    You should have received a copy of the GNU General Public License
#    along with ⊔net.  If not, see <http://www.gnu.org/licenses/>.
#
#    Acknowledgements:
#    * ECDSA has been adapted to Python3 and simplified for 512P curve only 
#      code inspired from:
#      Brian Warner  
#    * The PyCrypt library is far too complex for our needs so we used a code 
#      for AES inspired from:
#      Josh Davis ( http://www.josh-davis.org )
#      Laurent Haan (http://www.progressive-coding.com)
#    * QRcode is extented to PDF and SVG from the inspired code of:
#      Sam Curren (porting from Javascript)
#    * Encryption with ECC use an idea of jackjack-jj on github
#-----------------------------------------------------------------------------

# Short todo list
# - shift sha1 to sha256 in for signing
# - Frontend for 'Maires' (add change password, user reset)
# - Fix mairies list (380 errors)
# - Finish eurofranc/2015 pages
# - Prepare letter (both text and PDF) for Maires

import re, os, sys, urllib.parse, hashlib, http.client, base64, dbm.ndbm, datetime, functools, subprocess, time, smtplib, operator, random, getpass
import PyQt4.QtGui # only for GUI

__digest__ = base64.urlsafe_b64encode(hashlib.sha1(open(__file__, 'r', encoding='utf8').read().encode('utf8')).digest())[:10]
__app__    = os.path.basename(__file__)[:-3]
__dfprt__  = 80
__base__   = '/%s/%s_%s/' % (__app__, __app__, __dfprt__)
__ppc__    = 'eurofranc'
__email__  = 'contact@%s.fr' % __ppc__

_SVGNS     = 'xmlns="http://www.w3.org/2000/svg"'
_b58char   = '123456789abcdefghijkmnopqrstuvwxyzABCDEFGHJKLMNPQRSTUVWXYZ'
_root_id   = 'AdminJqjFdcY'
_root_pkey = 'AdMctT3bXbwrTBGkB5eKAG74qIqShRRy1nHa_NWCHsxmKhmZeE_aWgo_S251td8d6C5uti6TymQSSZvhmO1b19pI/AYYPFxkKL_13dnhBGXdFdmDQhQEZZbc1P7GDDrZZwU0FSGuwc53_AxHk1vVRte7bdmhzIcOUMUvO' 

_cur = {'€':b'A', '£':b'P', '$':b'D', '⊔':b'U', 'C':b'C'}

##### ENCODING #####
PAD = lambda s:(len(s)%2)*'0'+s[2:]

def i2b(x, n=1):
    "int to bytes with n padding"
    z = bytes.fromhex(PAD(hex(x)))
    return ((n-len(z))%n)*bytes.fromhex('00') + z

def b2i(x):
    "bytes to int"
    return int.from_bytes(x, 'big')

def s2b(x, n=1):
    "signed int to bytes with n padding"
    z = bytes.fromhex(PAD(hex(x + (1<<(8*n-1)))))
    return ((n-len(z))%n)*bytes.fromhex('00') + z

def b2s(x, n=1):
    "signed bytes to int"
    return int.from_bytes(x, 'big') - (1<<(8*n-1)) 

def itob64(n):
    "transform int to base64"
    return re.sub(b'=*$', b'', base64.urlsafe_b64encode(bytes.fromhex(PAD(hex(n)))))

def b64toi(c):
    "transform base64 to int"
    if c == '': return 0
    return int.from_bytes(base64.urlsafe_b64decode(c + b'='*((4-(len(c)%4))%4)), 'big')

def btob64(c):
    "bytes to base64"
    return base64.urlsafe_b64encode(c).decode('ascii').strip('=')

def b64tob(c):
    "base64 to bytes"
    return base64.urlsafe_b64decode(c + b'='*((4-(len(c)%4))%4))

def H(*tab):
    "hash"
    return int(hashlib.sha1(b''.join(tab)).hexdigest(), 16)

def datencode(n=0):
    "4 chars (minute precision)"
    return i2b(int(time.mktime(time.gmtime())/60 + 60*24*n), 4)

def datdecode(tt):
    "4 chars (minute precision)"
    return time.strftime('%d/%m/%y %H:%M', time.localtime(float(b2i(tt)*60)))

def is_after(d1, d2): 
    "_"
    return datdecode(d1) > datdecode(d2)

def random_b64():
    "20 chars url safe"
    return base64.urlsafe_b64encode(bytes.fromhex(hashlib.sha1(os.urandom(32)).hexdigest()[:30]))    

def hcode(m, s=10):
    "_"
    return (hashlib.sha1(m.encode('utf8')).digest())[:s]

def valencode(xi, p1, pf):
    "xi:7/p1:17/pf:32"
    assert (2*p1 < pf or xi==0) and xi<=100 and p1<(1<<17) and pf<(1<<32)
    return i2b((xi<<49) + (p1<<32) + pf, 7)

def valdecode(code):
    "xi:7/p1:17/pf:32"
    e = int.from_bytes(code, 'big')
    return ((e>>49) & 0x7F), ((e>>32) & 0x1FFFF), (e & 0xFFFFFFFF)

### OLD
def valencode1(xi, p1, pf):
    "xi:7/p1:15/pf:26"
    assert (2*p1 < pf or xi==0) and xi<=100 and p1<(1<<15) and pf<(1<<26)
    return i2b((xi<<41) + (p1<<26) + pf, 6)

def valdecode1(code):
    "xi:7/p1:15/pf:26"
    e = int.from_bytes(code, 'big')
    return ((e>>41) & 0x7F), ((e>>26) & 0x7FFF), (e & 0x3FFFFFF)
###

##### ECDSA NIST CURVE P-521 #####

_B = b'UZU-uWGOHJofkpohoLaFQO6i2nJbmbMV87i0iZGO8QnhVhk5Uex-k3sWUsC9O7G_BzVz34g9LDTx70Uf1GtQPwA'
_GX = b'xoWOBrcEBOnNnj7LZiOVtEKcZIE5BT-1Ifgor2BrTT26oUted-_nWSj-HcEnov-o3jNIs8GFakKb-X5-McLlvWY'
_GY = b'ARg5KWp4mjvABFyKX7QsfRvZmPVESVebRGgXr70XJz5mLJfucple9CZAxVC5AT-tB2E1PHCGonLCQIi-lHaf0WZQ'
_R = b'Af' + b'_'*42 + b'-lGGh4O_L5Zrf8wBSPcJpdA7tcm4iZxHrrtvtx6ROGQJ'

class Curve(): 
    "The curve of points satisfying y^2 = x^3 + a*x + b (mod p)"
    def __init__(self, p, a, b): self.p, self.a, self.b = p, a, b
    def has_pt(self, x, y): return (y*y - (x*x*x + self.a*x + self.b)) % self.p == 0

c521 = Curve(b64toi(b'Af' + b'_'*86), -3, b64toi(_B))

class Point():
    def __init__(self, curve, x, y, order = None):
        self.curve, self.x, self.y, self.order = curve, x, y, order
    def __add__(self, other):
        if other == INFINITY: return self
        if self == INFINITY: return other
        if self.x == other.x:
            if (self.y + other.y) % self.curve.p == 0: return INFINITY
            else: return self.double()
        p = self.curve.p
        l = ((other.y - self.y) * inverse_mod(other.x - self.x, p)) % p
        x3 = (l*l - self.x - other.x) % p
        y3 = (l*(self.x - x3) - self.y) % p
        return Point(self.curve, x3, y3)
    def __mul__(self, e):
        if self.order: e = e % self.order
        if e == 0 or self == INFINITY: return INFINITY
        e3, neg_self = 3*e, Point(self.curve, self.x, -self.y, self.order)
        i = 1 << (len(bin(e3))-4)
        result = self
        while i > 1:
            result = result.double()
            if (e3 & i) != 0 and (e & i) == 0: result = result + self
            if (e3 & i) == 0 and (e & i) != 0: result = result + neg_self
            i //= 2
        return result
    def __rmul__(self, other): return self * other
    def double(self):
        if self == INFINITY: return INFINITY
        p, a = self.curve.p, self.curve.a
        l = ((3 * self.x * self.x + a) * inverse_mod(2 * self.y, p)) % p
        x3 = (l*l - 2 * self.x) % p
        y3 = (l*(self.x - x3) - self.y) % p
        return Point(self.curve, x3, y3)

INFINITY = Point(None, None, None)  

class ecdsa:
    def __init__(self):
        self.gen = Point(c521, b64toi(_GX), b64toi(_GY), b64toi(_R))
        self.pkgenerator, self.pkorder = self.gen, self.gen.order

    def generate(self):
        secexp = randrange(self.gen.order)
        pp = self.gen*secexp
        self.pt, n = pp, self.gen.order
        if not n: raise 'Generator point must have order!'
        if not n * pp == INFINITY: raise 'Bad Generator point order!'
        if pp.x < 0 or n <= pp.x or pp.y < 0 or n <= pp.y: raise 'Out of range!'
        self.privkey = secexp

    def verify(self, sig, data):
        r, s, G, n = b2i(sig[:66]), b2i(sig[66:]), self.pkgenerator, self.pkorder
        if r < 1 or r > n-1 or s < 1 or s > n-1: return False
        c = inverse_mod(s, n)
        u1, u2 = (H(data) * c) % n, (r * c) % n
        z = u1 * G + u2 * self.pt
        return z.x % n == r

    def sign(self, data):
        rk, G, n = randrange(self.pkorder), self.pkgenerator, self.pkorder
        k = rk % n
        p1 = k * G
        r = p1.x
        s = (inverse_mod(k, n) * (H(data) + (self.privkey * r) % n)) % n
        assert s != 0 and r != 0
        return i2b(r, 66) + i2b(s, 66)

    def find_offset(self, x):
        p, a, b = b64toi(b'Af' + b'_'*86), -3, b64toi(_B)
        for offset in range(64):
            Mx = x + offset
            My2 = pow(Mx, 3, p) + a * Mx + b % p
            My = pow(My2, (p+1)//4, p)
            if c521.has_pt(Mx, My): return offset, My
        raise Exception('Y Not found')

    def encrypt(self, data):
        p, a, b, G, x = b64toi(b'Af' + b'_'*86), -3, b64toi(_B), self.pkgenerator, int.from_bytes(data, 'big')
        offset, y = self.find_offset(x)
        M, k = Point(c521, x + offset, y), randrange(self.pkorder)        
        p1, p2 = k*G, M + k*self.pt
        o1, o2 = p1.y&1, p2.y&1
        return bytes('%02X' % ((o1<<7) + (o2<<6) + offset), 'ascii') + i2b(p1.x, 66) + i2b(p2.x, 66)

    def decrypt(self, enctxt):
        oo, x1, x2 =  int(enctxt[:2], 16), b2i(enctxt[2:68]), b2i(enctxt[68:])
        o1, o2, offset, p, a, b = (oo & 0x80)>>7,(oo & 0x40)>>6, oo & 0x3F, b64toi(b'Af' + b'_'*86), -3, b64toi(_B)
        z1, z2 = pow(x1, 3, p) + a * x1 + b % p, pow(x2, 3, p) + a * x2 + b % p
        t1, t2 = pow(z1, (p+1)//4, p), pow(z2, (p+1)//4, p)
        y1, y2 = t1 if int(o1) == t1&1 else (-t1)%p, t2 if int(o2) == t2&1 else (-t2)%p
        p1, p2 = Point(c521, x1, - y1), Point(c521, x2, y2)
        u = p2 + self.privkey * p1
        return i2b(u.x-offset)

def inverse_mod(a, m):
    "_"
    if a < 0 or m <= a: a = a % m
    c, d = a, m
    uc, vc, ud, vd = 1, 0, 0, 1
    while c != 0:
        q, c, d = divmod(d, c) + (c,)
        uc, vc, ud, vd = ud - q*uc, vd - q*vc, uc, vc
    if ud > 0: return ud
    else: return ud + m

def randrange(order):
    "_"
    byts = (1+len('%x' % order))//2
    cand = b2i(os.urandom(byts))
    return cand//2 if cand >= order else cand

##### LOCAL AES-256 ##### (replace PyCrypto AES)
_IV = b'ABCDEFGHIJKLMNOP'

class AES:
    sbox =  [
        0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
        0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
        0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
        0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
        0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
        0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
        0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
        0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
        0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
        0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
        0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
        0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
        0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
        0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
        0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
        0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16 ]

    rsbox = [
        0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
        0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb,
        0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
        0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25,
        0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
        0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84,
        0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
        0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b,
        0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,
        0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85, 0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e,
        0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
        0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4,
        0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
        0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef,
        0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
        0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d ]

    Rcon = [
        0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 
        0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39, 
        0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a, 
        0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 
        0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 
        0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc, 
        0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 
        0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 
        0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94, 
        0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 
        0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 
        0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f, 
        0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04,
        0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 
        0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd, 
        0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb ]

    def rotate(self, word):
        c = word[0]
        for i in range(3): word[i] = word[i+1]
        word[3] = c	
        return word

    def core(self, word, iteration):
        word = self.rotate(word)
        for i in range(4): word[i] = self.sbox[word[i]]
        word[0] = word[0]^self.Rcon[iteration]
        return word

    def expandKey(self, key, expandedKeySize):
        currentSize, rconIteration, t, expandedKey = 32, 1, [0]*4, [0]*expandedKeySize
        for j in range(32): expandedKey[j] = key[j]
        while currentSize < expandedKeySize:
            for k in range(4): t[k] = expandedKey[(currentSize - 4) + k]
            if currentSize % 32 == 0:
                t = self.core(t, rconIteration)
                rconIteration += 1;
            if (currentSize % 32) == 16:
                for l in range(4): t[l] = self.sbox[t[l]]
            for m in range(4):
                expandedKey[currentSize] = expandedKey[currentSize - 32] ^ t[m]
                currentSize += 1
        return expandedKey

    def addRoundKey(self, state, roundKey):
        for i in range(16): state[i] ^= roundKey[i]
        return state

    def createRoundKey(self, expandedKey, roundKeyPointer):
        return [expandedKey[roundKeyPointer+i*4+j] for j in range(4) for i in range(4)]

    def g_mult(self, a, b):
        p = 0
        for counter in range(8):
            if (b & 1) == 1: p ^= a
            if p > 0x100: p ^= 0x100
            hi_bit_set = (a & 0x80)
            a <<= 1
            if a > 0x100: a ^= 0x100
            if hi_bit_set == 0x80: a ^= 0x1b
            if a > 0x100: a ^= 0x100
            b >>= 1
            if b > 0x100: b ^= 0x100
        return p

    def subBytes(self, state):
        for i in range(16): state[i] = self.sbox[state[i]]
        return state

    def shiftRows(self, state):
        for i in range(4): state = self.shiftRow(state, i*4, i)
        return state

    def shiftRow(self, state, pointer, nbr):
        for i in range(nbr):
            tmp = state[pointer]
            for j in range(3): state[pointer + j] = state[pointer + j+1]
            state[pointer + 3] = tmp
        return state

    def mixColumns(self, state):
        column = [0]*4
        for i in range(4):
            for j in range(4): column[j] = state[(j*4)+i]
            column = self.mixColumn(column)
            for k in range(4): state[(k*4)+i] = column[k]		
        return state;

    def mixColumn(self, col):
        mult, cpy = [2, 1, 1, 3], [0]*4
        for i in range(4): cpy[i] = col[i]
        col[0] = self.g_mult(cpy[0], mult[0]) ^ self.g_mult(cpy[3], mult[1]) ^ self.g_mult(cpy[2], mult[2]) ^ self.g_mult(cpy[1], mult[3])
        col[1] = self.g_mult(cpy[1], mult[0]) ^ self.g_mult(cpy[0], mult[1]) ^ self.g_mult(cpy[3], mult[2]) ^ self.g_mult(cpy[2], mult[3])
        col[2] = self.g_mult(cpy[2], mult[0]) ^ self.g_mult(cpy[1], mult[1]) ^ self.g_mult(cpy[0], mult[2]) ^ self.g_mult(cpy[3], mult[3])
        col[3] = self.g_mult(cpy[3], mult[0]) ^ self.g_mult(cpy[2], mult[1]) ^ self.g_mult(cpy[1], mult[2]) ^ self.g_mult(cpy[0], mult[3])
        return col
	
    def aes_round(self, state, roundKey):
        state = self.subBytes(state)
        state = self.shiftRows(state)
        state = self.mixColumns(state)
        state = self.addRoundKey(state, roundKey)
        return state
	
    def aes_main(self, state, expandedKey, nbrRounds):
        state, i = self.addRoundKey(state, self.createRoundKey(expandedKey, 0)), 1
        for i in range(1, nbrRounds): state = self.aes_round(state, self.createRoundKey(expandedKey, 16*i))
        state = self.subBytes(state)
        state = self.shiftRows(state)
        state = self.addRoundKey(state, self.createRoundKey(expandedKey, 16*nbrRounds))
        return state
	
    def enc(self, iput, key):
        output, block, nbrRounds = [0]*16, [0]*16, 14
        expandedKeySize = (16*(nbrRounds+1))
        for i in range(4):
            for j in range(4): block[(i+(j*4))] = iput[(i*4)+j]
        expandedKey = self.expandKey(key, expandedKeySize)
        block = self.aes_main(block, expandedKey, nbrRounds)
        for k in range(4):
            for l in range(4): output[(k*4)+l] = block[(k+(l*4))]
        return output
	
    def encrypt(self, stringIn, key):
        plain, iput, output, cipher  = [], [], [], [0]*16
        cipherOut, firstRound = [], True
        if stringIn != None:
            for j in range(1+(len(stringIn)-1)//16):
                start, end = j*16, j*16+16
                if j*16+16 > len(stringIn): end = len(stringIn)
                plain = (stringIn.encode('utf8'))[start:end]
                if firstRound: output, firstRound = self.enc(_IV, key), False
                else: output = self.enc(iput, key)
                for i in range(16):
                    if len(plain)-1 < i: cipher[i] = 0 ^ output[i]
                    elif len(output)-1 < i: cipher[i] = plain[i] ^ 0
                    elif len(plain)-1 < i and len(output) < i: cipher[i] = 0 ^ 0
                    else: cipher[i] = plain[i] ^ output[i]
                for k in range(end-start): cipherOut.append(cipher[k])
                iput = output
        return base64.urlsafe_b64encode(bytes(cipherOut))

    def decrypt(self, cIn, key):
        cipher, iput, output, plain, stringOut, fround, cipherIn = [], [], [], [0]*16, '', True, [i for i in base64.urlsafe_b64decode(cIn)]
        if cipherIn != None:
            for j in range(1+(len(cipherIn)-1)//16):
                start, end = j*16, j*16+16
                if j*16+16 > len(cipherIn): end = len(cipherIn)
                cipher = cipherIn[start:end]
                if fround: output, fround = self.enc(_IV, key), False
                else: output = self.enc(iput, key)
                for i in range(16):
                    if len(output)-1 < i: plain[i] = 0 ^ cipher[i]
                    elif len(cipher)-1 < i: plain[i] = output[i] ^ 0
                    elif len(output)-1 < i and len(cipher) < i: plain[i] = 0 ^ 0
                    else: plain[i] = output[i] ^ cipher[i]
                for k in range(end-start): stringOut += chr(plain[k])
                iput = output
        return stringOut.rstrip('@');

##### QRCODE #####

ERR_COR_L, ERR_COR_M, ERR_COR_Q, ERR_COR_H = 1, 0, 3, 2
MODE_NUMBER, MODE_ALPHA_NUM, MODE_8BIT_BYTE, MODE_KANJI = 1, 2, 4, 8
MODE_SIZE_SMALL  = { MODE_NUMBER: 10, MODE_ALPHA_NUM: 9,  MODE_8BIT_BYTE: 8,  MODE_KANJI: 8,}
MODE_SIZE_MEDIUM = { MODE_NUMBER: 12, MODE_ALPHA_NUM: 11, MODE_8BIT_BYTE: 16, MODE_KANJI: 10,}
MODE_SIZE_LARGE  = { MODE_NUMBER: 14, MODE_ALPHA_NUM: 13, MODE_8BIT_BYTE: 16, MODE_KANJI: 12,}
ALPHA_NUM = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ $%*+-./:'
TEXP = list(range(256))
TLOG = list(range(256))
for i in range(8): TEXP[i] = 1 << i
for i in range(8, 256): TEXP[i] = (TEXP[i - 4] ^ TEXP[i - 5] ^ TEXP[i - 6] ^ TEXP[i - 8])
for i in range(255): TLOG[TEXP[i]] = i
NUMBER_LENGTH = {3: 10, 2: 7, 1: 4}
RS_BLOCK_OFFSET = { ERR_COR_L: 0, ERR_COR_M: 1, ERR_COR_Q: 2, ERR_COR_H: 3 }
RS_BLOCK_TABLE = [ # L M Q H
    [1, 26, 19], [1, 26, 16], [1, 26, 13], [1, 26, 9],
    [1, 44, 34], [1, 44, 28], [1, 44, 22], [1, 44, 16],
    [1, 70, 55], [1, 70, 44], [2, 35, 17], [2, 35, 13],
    [1, 100, 80],[2, 50, 32], [2, 50, 24], [4, 25, 9],
    [1, 134, 108], [2, 67, 43], [2, 33, 15, 2, 34, 16], [2, 33, 11, 2, 34, 12], 
    [2, 86, 68], [4, 43, 27], [4, 43, 19], [4, 43, 15], 
    [2, 98, 78], [4, 49, 31], [2, 32, 14, 4, 33, 15], [4, 39, 13, 1, 40, 14], 
    [2, 121, 97], [2, 60, 38, 2, 61, 39], [4, 40, 18, 2, 41, 19], [4, 40, 14, 2, 41, 15], 
    [2, 146, 116], [3, 58, 36, 2, 59, 37], [4, 36, 16, 4, 37, 17], [4, 36, 12, 4, 37, 13], 
    [2, 86, 68, 2, 87, 69], [4, 69, 43, 1, 70, 44], [6, 43, 19, 2, 44, 20], [6, 43, 15, 2, 44, 16], 
    [4, 101, 81], [1, 80, 50, 4, 81, 51], [4, 50, 22, 4, 51, 23], [3, 36, 12, 8, 37, 13], 
    [2, 116, 92, 2, 117, 93], [6, 58, 36, 2, 59, 37], [4, 46, 20, 6, 47, 21], [7, 42, 14, 4, 43, 15], 
    [4, 133, 107], [8, 59, 37, 1, 60, 38], [8, 44, 20, 4, 45, 21], [12, 33, 11, 4, 34, 12], 
    [3, 145, 115, 1, 146, 116], [4, 64, 40, 5, 65, 41], [11, 36, 16, 5, 37, 17], [11, 36, 12, 5, 37, 13], 
    [5, 109, 87, 1, 110, 88], [5, 65, 41, 5, 66, 42], [5, 54, 24, 7, 55, 25], [11, 36, 12], 
    [5, 122, 98, 1, 123, 99], [7, 73, 45, 3, 74, 46], [15, 43, 19, 2, 44, 20], [3, 45, 15, 13, 46, 16], 
    [1, 135, 107, 5, 136, 108], [10, 74, 46, 1, 75, 47], [1, 50, 22, 15, 51, 23], [2, 42, 14, 17, 43, 15], 
    [5, 150, 120, 1, 151, 121], [9, 69, 43, 4, 70, 44], [17, 50, 22, 1, 51, 23], [2, 42, 14, 19, 43, 15], 
    [3, 141, 113, 4, 142, 114], [3, 70, 44, 11, 71, 45], [17, 47, 21, 4, 48, 22], [9, 39, 13, 16, 40, 14], 
    [3, 135, 107, 5, 136, 108], [3, 67, 41, 13, 68, 42], [15, 54, 24, 5, 55, 25], [15, 43, 15, 10, 44, 16], 
    [4, 144, 116, 4, 145, 117], [17, 68, 42], [17, 50, 22, 6, 51, 23], [19, 46, 16, 6, 47, 17], 
    [2, 139, 111, 7, 140, 112], [17, 74, 46], [7, 54, 24, 16, 55, 25], [34, 37, 13], 
    [4, 151, 121, 5, 152, 122], [4, 75, 47, 14, 76, 48], [11, 54, 24, 14, 55, 25], [16, 45, 15, 14, 46, 16], 
    [6, 147, 117, 4, 148, 118], [6, 73, 45, 14, 74, 46], [11, 54, 24, 16, 55, 25], [30, 46, 16, 2, 47, 17], 
    [8, 132, 106, 4, 133, 107], [8, 75, 47, 13, 76, 48], [7, 54, 24, 22, 55, 25], [22, 45, 15, 13, 46, 16], 
    [10, 142, 114, 2, 143, 115], [19, 74, 46, 4, 75, 47], [28, 50, 22, 6, 51, 23], [33, 46, 16, 4, 47, 17], 
    [8, 152, 122, 4, 153, 123], [22, 73, 45, 3, 74, 46], [8, 53, 23, 26, 54, 24], [12, 45, 15, 28, 46, 16], 
    [3, 147, 117, 10, 148, 118], [3, 73, 45, 23, 74, 46], [4, 54, 24, 31, 55, 25], [11, 45, 15, 31, 46, 16], 
    [7, 146, 116, 7, 147, 117], [21, 73, 45, 7, 74, 46], [1, 53, 23, 37, 54, 24], [19, 45, 15, 26, 46, 16], 
    [5, 145, 115, 10, 146, 116], [19, 75, 47, 10, 76, 48], [15, 54, 24, 25, 55, 25], [23, 45, 15, 25, 46, 16], 
    [13, 145, 115, 3, 146, 116], [2, 74, 46, 29, 75, 47], [42, 54, 24, 1, 55, 25], [23, 45, 15, 28, 46, 16], 
    [17, 145, 115], [10, 74, 46, 23, 75, 47], [10, 54, 24, 35, 55, 25], [19, 45, 15, 35, 46, 16], 
    [17, 145, 115, 1, 146, 116], [14, 74, 46, 21, 75, 47], [29, 54, 24, 19, 55, 25], [11, 45, 15, 46, 46, 16], 
    [13, 145, 115, 6, 146, 116], [14, 74, 46, 23, 75, 47], [44, 54, 24, 7, 55, 25], [59, 46, 16, 1, 47, 17], 
    [12, 151, 121, 7, 152, 122], [12, 75, 47, 26, 76, 48], [39, 54, 24, 14, 55, 25], [22, 45, 15, 41, 46, 16], 
    [6, 151, 121, 14, 152, 122], [6, 75, 47, 34, 76, 48], [46, 54, 24, 10, 55, 25], [2, 45, 15, 64, 46, 16],
    [17, 152, 122, 4, 153, 123], [29, 74, 46, 14, 75, 47], [49, 54, 24, 10, 55, 25], [24, 45, 15, 46, 46, 16],
    [4, 152, 122, 18, 153, 123], [13, 74, 46, 32, 75, 47], [48, 54, 24, 14, 55, 25], [42, 45, 15, 32, 46, 16],
    [20, 147, 117, 4, 148, 118], [40, 75, 47, 7, 76, 48], [43, 54, 24, 22, 55, 25], [10, 45, 15, 67, 46, 16],
    [19, 148, 118, 6, 149, 119], [18, 75, 47, 31, 76, 48], [34, 54, 24, 34, 55, 25], [20, 45, 15, 61, 46, 16]
]
PATTERN_POSITION_TABLE = [
    [], [6, 18], [6, 22], [6, 26], [6, 30], [6, 34],
    [6, 22, 38], [6, 24, 42], [6, 26, 46], [6, 28, 50], [6, 30, 54], [6, 32, 58], [6, 34, 62],
    [6, 26, 46, 66], [6, 26, 48, 70], [6, 26, 50, 74], [6, 30, 54, 78], [6, 30, 56, 82], [6, 30, 58, 86], [6, 34, 62, 90],
    [6, 28, 50, 72, 94], [6, 26, 50, 74, 98], [6, 30, 54, 78, 102], [6, 28, 54, 80, 106], [6, 32, 58, 84, 110], [6, 30, 58, 86, 114], [6, 34, 62, 90, 118],
    [6, 26, 50, 74, 98, 122], [6, 30, 54, 78, 102, 126], [6, 26, 52, 78, 104, 130], [6, 30, 56, 82, 108, 134],
    [6, 34, 60, 86, 112, 138], [6, 30, 58, 86, 114, 142], [6, 34, 62, 90, 118, 146],
    [6, 30, 54, 78, 102, 126, 150], [6, 24, 50, 76, 102, 128, 154], [6, 28, 54, 80, 106, 132, 158], [6, 32, 58, 84, 110, 136, 162],
    [6, 26, 54, 82, 110, 138, 166], [6, 30, 58, 86, 114, 142, 170]
]
G15 = ((1 << 10) | (1 << 8) | (1 << 5) | (1 << 4) | (1 << 2) | (1 << 1) | (1 << 0))
G18 = ((1 << 12) | (1 << 11) | (1 << 10) | (1 << 9) | (1 << 8) | (1 << 5) | (1 << 2) | (1 << 0))
G15_MASK = (1 << 14) | (1 << 12) | (1 << 10) | (1 << 4) | (1 << 1)

def BCH_type_info(data):
    d = data << 10
    while BCH_digit(d) - BCH_digit(G15) >= 0: d ^= (G15 << (BCH_digit(d) - BCH_digit(G15)))
    return ((data << 10) | d) ^ G15_MASK

def BCH_type_number(data):
    d = data << 12
    while BCH_digit(d) - BCH_digit(G18) >= 0: d ^= (G18 << (BCH_digit(d) - BCH_digit(G18)))
    return (data << 12) | d

def BCH_digit(data):
    digit = 0
    while data != 0:
        digit += 1
        data >>= 1
    return digit

def pattern_position(version):
    return PATTERN_POSITION_TABLE[version - 1]

def mask_func(pattern):
    if pattern == 0: return lambda i, j: (i + j) % 2 == 0 
    if pattern == 1: return lambda i, j: i % 2 == 0 
    if pattern == 2: return lambda i, j: j % 3 == 0
    if pattern == 3: return lambda i, j: (i + j) % 3 == 0
    if pattern == 4: return lambda i, j: (int(i / 2) + int(j / 3)) % 2 == 0
    if pattern == 5: return lambda i, j: (i * j) % 2 + (i * j) % 3 == 0
    if pattern == 6: return lambda i, j: ((i * j) % 2 + (i * j) % 3) % 2 == 0
    if pattern == 7: return lambda i, j: ((i * j) % 3 + (i + j) % 2) % 2 == 0

def length_in_bits(mode, version):
    if version < 10: mode_size = MODE_SIZE_SMALL
    elif version < 27: mode_size = MODE_SIZE_MEDIUM
    else: mode_size = MODE_SIZE_LARGE
    return mode_size[mode]

def lost_point1(modules):
    modules_count, lost_point, darkCount = len(modules), 0, 0
    for row in range(modules_count):
        for col in range(modules_count):
            sameCount, dark = 0, modules[row][col]
            for r in range(-1, 2):
                if row + r < 0 or modules_count <= row + r: continue
                for c in range(-1, 2):
                    if col + c < 0 or modules_count <= col + c: continue
                    if r == 0 and c == 0: continue
                    if dark == modules[row + r][col + c]: sameCount += 1
            if sameCount > 5: lost_point += (3 + sameCount - 5)
    for row in range(modules_count - 1):
        for col in range(modules_count - 1):
            count = 0
            if modules[row][col]: count += 1
            if modules[row + 1][col]: count += 1
            if modules[row][col + 1]: count += 1
            if modules[row + 1][col + 1]: count += 1
            if count == 0 or count == 4: lost_point += 3
    for row in range(modules_count):
        for col in range(modules_count - 6):
            if (modules[row][col]
                    and not modules[row][col + 1]
                    and modules[row][col + 2]
                    and modules[row][col + 3]
                    and modules[row][col + 4]
                    and not modules[row][col + 5]
                    and modules[row][col + 6]):
                lost_point += 40
    for col in range(modules_count):
        for row in range(modules_count - 6):
            if (modules[row][col]
                    and not modules[row + 1][col]
                    and modules[row + 2][col]
                    and modules[row + 3][col]
                    and modules[row + 4][col]
                    and not modules[row + 5][col]
                    and modules[row + 6][col]):
                lost_point += 40
    for col in range(modules_count):
        for row in range(modules_count):
            if modules[row][col]: darkCount += 1
    return lost_point + abs(100 * darkCount / modules_count / modules_count - 50) * 2

class QRData:
    def __init__(self, data, mode=None):
        if data.isdigit(): auto_mode = MODE_NUMBER
        elif re.match('^[%s]*$' % re.escape(ALPHA_NUM), data): auto_mode = MODE_ALPHA_NUM
        else: auto_mode = MODE_8BIT_BYTE
        self.mode, self.data = auto_mode if mode is None else mode, data
    def __len__(self):
        return len(self.data)
    def write(self, buffer):
        if self.mode == MODE_NUMBER:
            for i in range(0, len(self.data), 3):
                chars = self.data[i:i + 3]
                bit_length = NUMBER_LENGTH[len(chars)]
                buffer.put(int(chars), bit_length)
        elif self.mode == MODE_ALPHA_NUM:
            for i in range(0, len(self.data), 2):
                chars = self.data[i:i + 2]
                if len(chars) > 1: buffer.put(ALPHA_NUM.find(chars[0]) * 45 + ALPHA_NUM.find(chars[1]), 11)
                else: buffer.put(ALPHA_NUM.find(chars), 6)
        else:
            for c in self.data:
                buffer.put(ord(c), 8)

class BitBuffer:
    def __init__(self): self.buffer, self.length = [], 0
    def get(self, index): return ((self.buffer[int(index/8)] >> (7 - index % 8)) & 1) == 1
    def put(self, num, length): 
        for i in range(length): self.put_bit(((num >> (length - i - 1)) & 1) == 1)
    def __len__(self): return self.length
    def put_bit(self, bit):
        buf_index = self.length // 8
        if len(self.buffer) <= buf_index: self.buffer.append(0)
        if bit: self.buffer[buf_index] |= (0x80 >> (self.length % 8))
        self.length += 1

def create_bytes(buffer, rs_b):
    offset, maxDcCount, maxEcCount, totalCodeCount, dcdata, ecdata = 0, 0, 0, 0, [0] * len(rs_b), [0] * len(rs_b)
    for r in range(len(rs_b)):
        dcCount = rs_b[r].data_count
        ecCount = rs_b[r].total_count - dcCount
        maxDcCount, maxEcCount, dcdata[r] = max(maxDcCount, dcCount), max(maxEcCount, ecCount), [0] * dcCount
        for i in range(len(dcdata[r])): dcdata[r][i] = 0xff & buffer.buffer[i + offset]
        offset += dcCount
        rsPoly = Poly([1], 0) 
        for i in range(ecCount): rsPoly = rsPoly * Poly([1, TEXP[i]], 0)
        modPoly = Poly(dcdata[r], len(rsPoly) - 1) % rsPoly
        ecdata[r] = [0] * (len(rsPoly) - 1)
        for i in range(len(ecdata[r])):
            modIndex = i + len(modPoly) - len(ecdata[r])
            ecdata[r][i] = modPoly[modIndex] if (modIndex >= 0) else 0
    for b in rs_b: totalCodeCount += b.total_count
    data, index = [None] * totalCodeCount, 0
    for i in range(maxDcCount):
        for r in range(len(rs_b)):
            if i < len(dcdata[r]):
                data[index] = dcdata[r][i]
                index += 1
    for i in range(maxEcCount):
        for r in range(len(rs_b)):
            if i < len(ecdata[r]):
                data[index] = ecdata[r][i]
                index += 1
    return data

class DataOverflowError(Exception):
    pass

def create_data(version, error_correction, data_list):
    rs_b, buffer, total_data_count, PAD0, PAD1 = rs_blocks(version, error_correction), BitBuffer(), 0, 0xEC, 0x11
    for data in data_list:
        buffer.put(data.mode, 4)
        buffer.put(len(data), length_in_bits(data.mode, version))
        data.write(buffer)
    for block in rs_b: total_data_count += block.data_count
    if len(buffer) > total_data_count * 8: raise DataOverflowError()
    if len(buffer) + 4 <= total_data_count * 8: buffer.put(0, 4)
    while len(buffer) % 8: buffer.put_bit(False)
    while True:
        if len(buffer) >= total_data_count * 8: break
        buffer.put(PAD0, 8)
        if len(buffer) >= total_data_count * 8: break
        buffer.put(PAD1, 8)
    return create_bytes(buffer, rs_b)

class Poly:
    def __init__(self, num, shift):
        offset = 0
        while offset < len(num) and num[offset] == 0: offset += 1
        self.num = [0] * (len(num) - offset + shift)
        for i in range(len(num) - offset): self.num[i] = num[i + offset]
    def __getitem__(self, index):
        return self.num[index]
    def __len__(self): return len(self.num)
    def __mul__(self, e):
        num = [0] * (len(self) + len(e) - 1)
        for i in range(len(self)):
            for j in range(len(e)): num[i + j] ^= TEXP[(TLOG[self[i]] + TLOG[e[j]]) % 255]
        return Poly(num, 0)
    def __mod__(self, e):
        if len(self) - len(e) < 0: return self
        ratio, num = TLOG[self[0]] - TLOG[e[0]], [0] * len(self)
        for i in range(len(self)): num[i] = self[i]
        for i in range(len(e)): num[i] ^= TEXP[(TLOG[e[i]] + ratio) % 255]
        return Poly(num, 0) % e

class RSBlock:
    def __init__(self, total_c, data_c):
        self.total_count, self.data_count = total_c, data_c

def rs_blocks(version, error_correction):
    offset = RS_BLOCK_OFFSET[error_correction]
    rs_b, blocks = RS_BLOCK_TABLE[(version - 1) * 4 + offset], []
    for i in range(0, len(rs_b), 3):
        count, total_count, data_count = rs_b[i:i + 3]
        for j in range(count): blocks.append(RSBlock(total_count, data_count))
    return blocks

class QRCode:
    def __init__(self, data='hello', error_co=0):
        self.version, self.error_co, size, self.m, self.m_count, self.data_cache, self.data_list = None, int(error_co), 1, None, 0, None, []
        self.data_list.append(QRData(data))
        while True:
            try: self.data_cache = create_data(size, self.error_co, self.data_list)
            except: size += 1
            else:
                self.version = size
                break
        self.makeImpl(False, self.best_mask_pattern())

    def makeImpl(self, test, mask_pattern):
        self.m_count = self.version * 4 + 17
        self.m = [None] * self.m_count
        for row in range(self.m_count):
            self.m[row] = [None] * self.m_count
            for col in range(self.m_count): self.m[row][col] = None   
        self.setup_position_probe_pattern(0, 0)
        self.setup_position_probe_pattern(self.m_count - 7, 0)
        self.setup_position_probe_pattern(0, self.m_count - 7)
        self.setup_position_adjust_pattern()
        self.setup_timing_pattern()
        self.setup_type_info(test, mask_pattern)
        if self.version >= 7: self.setup_type_number(test)
        if self.data_cache is None: self.data_cache = create_data(self.version, self.error_co, self.data_list)
        self.map_data(self.data_cache, mask_pattern)

    def setup_position_probe_pattern(self, row, col):
        for r in range(-1, 8):
            if row + r <= -1 or self.m_count <= row + r: continue
            for c in range(-1, 8):
                if col + c <= -1 or self.m_count <= col + c: continue
                self.m[row + r][col + c] = True if (0 <= r and r <= 6 and (c == 0 or c == 6) or (0 <= c and c <= 6 and (r == 0 or r == 6)) or (2 <= r and r <= 4 and 2 <= c and c <= 4)) else False

    def best_mask_pattern(self):
        min_lost_point, pattern = 0, 0
        for i in range(8):
            self.makeImpl(True, i)
            lost_point = lost_point1(self.m)
            if i == 0 or min_lost_point > lost_point: min_lost_point, pattern = lost_point, i
        return pattern

    def svg(self, ox=0, oy=0, d=2, txt=''):
        o, mc = '<svg %s width="%s" height="%s">\n' % (_SVGNS, ox+d*self.m_count, oy+d*self.m_count), self.m_count
        for r in range(mc):
            k = 0
            for c in range(mc):
                if self.m[r][c]: k += 1
                elif k > 0:
                    o += '<rect x="%d" y="%d" width="%d" height="%d"/>\n' % (ox+(c-k)*d, oy+r*d, k*d, d)
                    k = 0
            if k > 0: o += '<rect x="%d" y="%d" width="%d" height="%d"/>\n' % (ox+(mc-k)*d, oy+r*d, k*d, d)
        if txt:
            o += '<text x="%s" y="%s" style="font-size:32;fill:gray" >%s</text>\n' % (ox, oy + 40 + d*mc, txt)
        return o + '</svg>\n'

    def pdf(self, ox=0, oy=0, d=10, size=False, color = b'0 0 0'):
        o, mc = color + b' rg ', self.m_count
        if size:
            o += bytes('q .9 .9 .9 rg BT 1 0 0 1 2 2 Tm /F1 3 Tf (%d) Tj ET Q ' % self.m_count, 'ascii')
        for r in range(mc):
            k = 0
            for c in range(mc):
                if self.m[r][c]: k += 1
                elif k > 0:
                    o += bytes('%d %d %d %d re ' % (ox+(c-k)*d, oy-r*d, k*d, d), 'ascii')
                    k = 0
            if k > 0: o += bytes('%d %d %d %d re ' % (ox+(mc-k)*d, oy-r*d, k*d, d), 'ascii')
        return o + b'f '

    def setup_timing_pattern(self):
        for r in range(8, self.m_count - 8):
            if self.m[r][6] != None: continue
            self.m[r][6] = (r % 2 == 0)
        for c in range(8, self.m_count - 8):
            if self.m[6][c] != None: continue
            self.m[6][c] = (c % 2 == 0)

    def setup_position_adjust_pattern(self):
        pos = pattern_position(self.version)
        for i in range(len(pos)):
            for j in range(len(pos)):
                row, col = pos[i], pos[j]
                if self.m[row][col] != None: continue
                for r in range(-2, 3):
                    for c in range(-2, 3):
                        self.m[row + r][col + c] = True if (r == -2 or r == 2 or c == -2 or c == 2 or (r == 0 and c == 0)) else False

    def setup_type_number(self, test):
        bits = BCH_type_number(self.version)
        for i in range(18): self.m[i // 3][i % 3 + self.m_count - 8 - 3] = (not test and ((bits >> i) & 1) == 1)
        for i in range(18): self.m[i % 3 + self.m_count - 8 - 3][i // 3] = (not test and ((bits >> i) & 1) == 1)

    def setup_type_info(self, test, mask_pattern):
        bits = BCH_type_info((self.error_co << 3) | mask_pattern)
        for i in range(15): 
            mod = (not test and ((bits >> i) & 1) == 1)
            if i < 6: self.m[i][8] = mod
            elif i < 8: self.m[i + 1][8] = mod
            else: self.m[self.m_count - 15 + i][8] = mod
        for i in range(15): 
            mod = (not test and ((bits >> i) & 1) == 1)
            if i < 8: self.m[8][self.m_count - i - 1] = mod
            elif i < 9: self.m[8][15 - i - 1 + 1] = mod
            else: self.m[8][15 - i - 1] = mod
        self.m[self.m_count - 8][8] = (not test) 

    def map_data(self, data, mask_pattern):
        inc, row, bitIndex, byteIndex, mask_func1 = -1, self.m_count - 1, 7, 0, mask_func(mask_pattern)
        for col in range(self.m_count - 1, 0, -2):
            if col == 6: col -= 1
            while True:
                for c in range(2):
                    if self.m[row][col - c] == None:
                        dark = False
                        if byteIndex < len(data): dark = (((data[byteIndex] >> bitIndex) & 1) == 1)
                        if mask_func1(row, col - c): dark = not dark
                        self.m[row][col - c] = dark
                        bitIndex -= 1
                        if bitIndex == -1:
                            byteIndex += 1
                            bitIndex = 7
                row += inc
                if row < 0 or self.m_count <= row:
                    row -= inc
                    inc = -inc
                    break

##### API #####

def send(host='localhost', data=''):
    "_"
    co, serv = http.client.HTTPConnection(host), '/' 
    co.request('POST', serv, urllib.parse.quote(data))
    return co.getresponse().read().decode('utf8')    

def send_get(host='localhost', data=''):
    "_"
    co = http.client.HTTPConnection(host)
    co.request('GET', '/' + urllib.parse.quote(data))
    return co.getresponse().read()    

def add_local_id():
    "_"
    pp1, pp2, cm, k, db, ok, notdone = '', '', b'', ecdsa(), dbm.open('keys', 'c'), True, True
    while pp1 != pp2 or len(pp1) < 4: pp1, pp2 = getpass.getpass('Select a passphrase? '), getpass.getpass('The passphrase again? ')
    if os.path.isfile('found_id.txt'):
        for l in open('found_id.txt').readlines():
            cm, tab = b64tob(bytes(l[:12], 'ascii')), l[16:].split('/')
            if cm not in db:
                print ('Static Id: %s' % l[:12])
                if input('Select this id or another ? [y/n]: ') == 'y':
                    #pp = getpass.getpass('Select root passphrase? ')
                    #intpriv = int(AES().decrypt(b64tob(bytes(tab[2].strip(), 'ascii')), hashlib.sha256(pp.encode('utf8')).digest()))
                    intpriv = b64toi(bytes(tab[2].strip(), 'ascii'))
                    #intpriv = int(tab[2].strip())
                    prv = AES().encrypt('%s' % intpriv, hashlib.sha256(pp1.encode('utf8')).digest())
                    ptx, pty = b64toi(bytes(tab[0].strip(), 'ascii')), b64toi(bytes(tab[1].strip(), 'ascii'))
                    #ptx, pty = int(tab[0].strip()), int(tab[1].strip())
                    db[cm] = i2b(ptx, 66) + i2b(pty, 66) + prv
                    #db[cm] = b''.join([b64tob(bytes(x, 'ascii')) for x in tab[:2]]) + prv
                    notdone = False
                    print ('%s added' % l[:12])
                    break
    if notdone:
        while (cm in db) or ok:
            k.generate()
            cm = i2b(k.pt.y)[-9:]
            print ('Id: %s' % btob64(cm))
            ok = not (input('Select this id or another ? [y/n]: ') == 'y')
        db[cm] = i2b(k.pt.x, 66) + i2b(k.pt.y, 66) + AES().encrypt('%s' % k.privkey, hashlib.sha256(pp1.encode('utf8')).digest())
        print ('%s added' % btob64(cm))
    if b'user' not in db: db[b'user'] = cm
    if b'host' not in db: db[b'host'] = b'cup'    
    db.close()

def add_local_id2(pp):
    "for gui"
    cm, k, db = b'', ecdsa(), dbm.open('keys', 'c')
    k.generate()
    cm = i2b(k.pt.y)[-9:]
    if cm not in db:
        db[cm] = i2b(k.pt.x, 66) + i2b(k.pt.y, 66) + AES().encrypt('%s' % k.privkey, hashlib.sha256(pp.encode('utf8')).digest())
        print ('%s added' % btob64(cm))
    db.close()

def list_local_ids(node):
    "_"
    if os.path.isfile('keys'):
        db = dbm.open('keys', 'c')
        print ('Autority: %s, Currency: %s, Host: \'%s\', You have %d user IDs:' % (_root_id, db['cry'].decode('utf8'), db['host'].decode('ascii'), len(db.keys())-3))
        for x in filter(lambda i:len(i)==9, db.keys()):
            bl = send(node, '=' + btob64(x))
            print (btob64(x), '%20s' % bl if db['user'] != x else '%20s\t*' % bl )
        db.close()
    else:
        print ('Use \'./%s add\' for adding an ID' % __app__) 

def get_unique(dk, rid):
    "_"
    out = [u for u in filter(lambda i:re.match(rid, btob64(i)), dk.keys())]
    return out[0] if len(out) == 1 else None

def set(k, h):
    "_"
    d = dbm.open('keys', 'c') 
    if k == 'user':
        src = get_unique(d, h)
        if src: 
            d[k] = src
            print ('%s->%s' % (k, btob64(src)))
    elif k == 'host':
        d[k] = h
        print ('%s->%s' % (k, h))
    elif k == 'cry':
        d[k] = h
        print ('%s->%s' % (k, h))
    d.close()

def readdb(arg, ascii=False):
    "_"
    d = dbm.open(arg)
    if ascii:
        #for x in d.keys(): print (x.decode('ascii'), '->', d[x].decode('ascii'))
        for x in d.keys():
            if reg(re.match(r'(.+) - (\d{4,5})', x.decode('utf8'))):
                print (reg.v.group(2), reg.v.group(1), '->', d[x].decode('utf8'))
            else:
                print (x.decode('utf8'), '->', d[x].decode('utf8'))
        #for x in d.keys(): print (x, '->', d[x])
    else:
        for x in d.keys(): print ('%02d:%03d' % (len(x), len(d[x])), btob64(x), '->', btob64(d[x]))

def get_host():
    "_"
    db = dbm.open('keys')
    host = db['host']
    db.close()
    return host.decode('utf8')

def certif(node, rid):
    "_"
    db, k, dat = dbm.open('keys'), ecdsa(), datencode()
    src, res = db['user'], send(node, '?' + rid)
    if res: 
        prv, pub, dst, pp = db[src][132:], db[src][:132], b64tob(bytes(res, 'ascii')), getpass.getpass('Passphrase for \'%s\'? ' % btob64(src))
        print ('...please wait')
        age = 1967
        k.privkey, msg = int(AES().decrypt(prv, hashlib.sha256(pp.encode('utf8')).digest())), dst + datencode(365) + src + i2b(age, 2) + hcode('%s 167071927202809' % age)
        print (send(node, '.' + btob64(msg + k.sign(msg))))
    else:
        print('unknown recipient')
    db.close()

def buy(node, rid, prc):
    "_"
    db, k, dat = dbm.open('keys'), ecdsa(), datencode()
    cry = _cur[db['cry'].decode('utf8')] if db['cry'].decode('utf8') in _cur else db['cry']
    src, pri, res = db['user'], int(prc*100) if cry == b'A' else int(prc), send(node, '?' + rid)
    if res: 
        prv, pub, dst, pp = db[src][132:], db[src][:132], b64tob(bytes(res, 'ascii')), getpass.getpass('Passphrase for \'%s\'? ' % btob64(src))
        m = input('Message (20 chars maxi)? ')
        print ('...please wait')
        k.privkey, msg = int(AES().decrypt(prv, hashlib.sha256(pp.encode('utf8')).digest())), datencode() + src + cry + dst + i2b(pri, 3) + bytes(m, 'utf8')[:20]
        print (send(node, '+' + btob64(msg + k.sign(msg)))) 
    else:
        print('unknown recipient')
    db.close()

def message(node, rid, m=''):
    "_"
    db, k, dat = dbm.open('keys'), ecdsa(), datencode()
    cry, src, res = b'C', db['user'], send(node, '?' + rid)
    if res: 
        prv, pub, dst, pp = db[src][132:], db[src][:132], b64tob(bytes(res, 'ascii')), getpass.getpass('Passphrase for \'%s\'? ' % btob64(src))
        print ('...please wait')
        k.privkey, msg = int(AES().decrypt(prv, hashlib.sha256(pp.encode('utf8')).digest())), datencode() + src + cry + dst + bytes(m, 'utf8')[:23]
        print (send(node, '+' + btob64(msg + k.sign(msg)))) 
    else:
        print('unknown recipient')
    db.close()

def message2(node, sc, rid, m, pp):
    "_"
    db, k, dat = dbm.open('keys'), ecdsa(), datencode()
    cry, src, res = b'C', b64tob(bytes(sc, 'ascii')), send(node, '?' + rid)
    if res: 
        prv, pub, dst = db[src][132:], db[src][:132], b64tob(bytes(res, 'ascii'))
        k.privkey, msg = int(AES().decrypt(prv, hashlib.sha256(pp.encode('utf8')).digest())), datencode() + src + cry + dst + bytes(m, 'utf8')[:23]
        print (send(node, '+' + btob64(msg + k.sign(msg)))) 
    else:
        print('unknown recipient')
    db.close()

def buy2(node, sc, rid, pc, cry, pp, mes=''):
    "gui call"
    prc, src, db, k, dat, cry = float(pc), b64tob(bytes(sc, 'ascii')), dbm.open('keys'), ecdsa(), datencode(), _cur[cry]
    pri, res = int(prc*100) if cry == b'A' else int(prc), send(node, '?' + rid)
    if res: 
        prv, pub, dst = db[src][132:], db[src][:132], b64tob(bytes(res, 'ascii'))
        k.privkey, msg = int(AES().decrypt(prv, hashlib.sha256(pp.encode('utf8')).digest())), datencode() + src + cry + dst + i2b(pri, 3) + bytes(mes, 'utf8')[:20]
        print ('http://eurofranc.fr/+' + btob64(msg + k.sign(msg)))
        print (send(node, '+' + btob64(msg + k.sign(msg)))) 
    db.close()

def buyig (node, ig):
    "_"
    db, k = dbm.open('keys'), ecdsa()
    src, res = db['user'], send(node, '!' + ig)
    if res:
        prv, pub, rig, pp = db[src][132:], db[src][:132], b64tob(bytes(res, 'ascii')), getpass.getpass('Passphrase for \'%s\'? ' % btob64(src))
        print ('...please wait')
        k.privkey, msg = int(AES().decrypt(prv, hashlib.sha256(pp.encode('utf8')).digest())), rig + src + datencode()
        print (send(node, '*' + btob64(msg + k.sign(msg))))
        #    url = k.decrypt(b64tob(bytes(res, 'ascii'))).decode('ascii')
        #    print ('http://%s/%s' % (node, url))
        #    toto = send_get(node, url)
        #    open('toto.pdf', 'wb').write(toto)
    else:
        print('unknown ig recipient')
    db.close()

def buyig2 (node, sc, ig, pp):
    "gui call"
    src = b64tob(bytes(sc, 'ascii'))
    db, k = dbm.open('keys'), ecdsa()
    res = send(node, '!' + ig)
    if res:
        prv, pub, rig = db[src][132:], db[src][:132], b64tob(bytes(res, 'ascii'))
        k.privkey, msg = int(AES().decrypt(prv, hashlib.sha256(pp.encode('utf8')).digest())), rig + src + datencode()
        print (send(node, '*' + btob64(msg + k.sign(msg))))
    db.close()

def postig(node, p1, pf, xi):
    "_"
    db, k = dbm.open('keys'), ecdsa()
    src = db['user']
    prv, pub, pp = db[src][132:], db[src][:132], getpass.getpass('Passphrase for \'%s\'? ' % btob64(src))
    url = input('url? ')
    msg = hcode(url) + src + datencode() + valencode(xi, p1, pf)
    print ('...please wait')
    k.privkey = int(AES().decrypt(prv, hashlib.sha256(pp.encode('utf8')).digest()))
    print (send(node, '&' + btob64(msg + k.sign(msg)) + url))
    db.close()

def postig2(node, sc, p1, pf, xi, url, pp):
    "_"
    db, k, src = dbm.open('keys'), ecdsa(), b64tob(bytes(sc, 'ascii'))
    prv, pub = db[src][132:], db[src][:132]
    msg = hcode(url) + src + datencode() + valencode(xi, p1, pf)
    k.privkey = int(AES().decrypt(prv, hashlib.sha256(pp.encode('utf8')).digest()))
    print (send(node, '&' + btob64(msg + k.sign(msg)) + url))
    db.close()

def register(node):
    "_"
    db = dbm.open('keys')
    for x in filter(lambda i:len(i)==9, db.keys()): print (send(node, '@' + btob64(db[x][:132])))
    db.close()

def is_future(da):
    return int(time.mktime(time.gmtime())) < b2i(da)*60

def debt(d, cm, cry=b'A'):
    "_"
    du, dc, dbt = d['pub'], d['crt'], 0
    if cm in dc and len(dc[cm]) == 144:
        root, k = dc[b'_'], ecdsa()
        k.pt = Point(c521, b2i(du[root][:66]), b2i(du[root][66:]+root))
        if is_future(dc[cm][:4]) and k.verify(dc[cm][12:], cm + dc[cm][:12]): dbt = b2i(dc[cm][4:12])
        #if k.verify(dc[cm][12:], cm + dc[cm][:12]): dbt = b2i(dc[cm][4:12])
    return dbt

def is_active(cm):
    "_"
    du, dt, k = dbm.open(__base__+'pub'), dbm.open(__base__+'trx'), ecdsa()
    for t in dt.keys():
        src, dst = t[4:], dt[t][:9]
        k.pt = Point(c521, b2i(du[src][:66]), b2i(du[src][66:]+src))
        if (src == cm or dst == cm) and k.verify(dt[t][13:], t + dt[t][:13]):
            du.close(), dt.close()
            return True
    du.close(), dt.close()
    return False

def style_html(bg=True):
    "_"
    o = '<style type="text/css">@import url(http://fonts.googleapis.com/css?family=Schoolbell);h1,h2,p,li,i,b,a,div,input,td,th,footer,svg{font-family:"Lucida Grande", "Lucida Sans Unicode", Helvetica, Arial, Verdana, sans-serif}a.mono,p.mono,td.mono,b.mono{font-family:"Lucida Concole",Courier;font-weight:bold}a.name{margin:50}a{color:DodgerBlue;text-decoration:none}p.alpha{font-family:Schoolbell;color:#F87217;font-size:26pt;position:absolute;top:115;left:80}div.qr,a.qr{position:absolute;top:0;right:0;margin:15}p.note{font-size:9}p.msg{font-size:12;position:absolute;top:0;right:120;color:#F87217}p.stat{font-size:9;position:absolute;top:0;right:20;color:#999}input{font-size:28;margin:3}input.txt{width:200}input.digit{width:120;text-align:right}input.simu{width:120;text-align:right}input[type=checkbox]{width:50}input[type=submit]{color:white;background-color:#AAA;border:none;border-radius:8px;padding:3}p,li{margin:10;font-size:18;color:#333}b.red{color:red}b.green{color:green}b.blue{color:blue}b.bigorange{font-size:32;color:#F87217}b.biggreen{font-size:32;color:green}b.huge{position:absolute;top:15;left:76;font-size:90;}#wrap{overflow:hidden}a.ppc{font-weight:bold;font-size:.9em}a.ppc:after{font-weight:normal;content:"Cash"}#lcol{float:left;width:360;padding:4}#rcol{margin-left:368;padding:4}footer{bottom:0;color:#444;font-size:10;padding:4}table{margin:1;border:2px solid #999;border-collapse:collapse; background-color:white; opacity:.7}td,th{font-size:11pt;border:1px solid #666;padding:2pt}th{background-color:#DDD}td.num{font-size:12;text-align:right}#c1{float:left;width:23%;padding:1%}#c2{float:left;width:23%;padding:1%}#c3{float:left;width:23%;padding:1%}#c4{float:left;width:23%;padding:1%}h1{color:#888;font-size:25;margin:10 0 0 6}h2{color:#AAA;font-size:18;margin:5 0 0 30}svg{background-color:white}img.book{border:2px outset}text{font-size:18pt}body{margin:0}euro:after{font-size:60%;vertical-align:30%;content:"f";}'
    if bg:
        o += 'body{color:black;background-color:white;background-image:url(http://cupfoundation.net/fond.png);background-repeat:no-repeat}' 
    return o + '</style>'

def style():
    "_"
    return '<style>@import url(http://fonts.googleapis.com/css?family=Schoolbell);h1{font-size:64pt;text-align:center;font-family:Schoolbell}div,body{margin:0}p{font-family:arial;font-size:16pt;text-align:center;margin:0;margin-top:5}.page{position:relative;padding-top:60;padding-bottom:20}.aa{background-color:#22AA22;color:#FFFFFF}.bb{background-color:#22AAAA;color:#AA2222}.cc{background-color:#EEEE22;color:#2222AA}.dd{background-color:#AAEEEE;color:#555555}.foot{background-color:#555555;color:#CCCCCC}.note{font-family:arial;font-size:8pt;margin:0;margin-left:20;text-align:left}a{color:DodgerBlue;text-decoration:none}a.id{font-family:"Lucida Concole",Courier;font-weight:bold;color:White;text-decoration:none;background:black;padding:5;border-radius:7px}.header{position:fixed;top:0;left:0;margin:0;color:white}</style>'

def ibank():
    "_"
    o = '<div class="page dd"><h1>1- Créez un ID</h1><p>Par sécurité, un identifiant (ID) n\'est jamais créé en ligne mais toujours localement<sup>1</sup></p><p><a href="zzzz">Téléchargez</a> pour cela l\'application gratuite. Choisissez un mot de passe et ne le communiquez à personne</p><p>Vous pouvez créer autant d\'IDs que vous le desirez, leur solde initial est toujours nul</p><p> Ne faites confiance à personne, même pas à nous ! Inspectez notre <a href="dsd">code</a></p><p>————</p><p><i>Nous créditons sur votre demande 1€ et 1⊔ pour tester l\'application<sup>2</sup></i></p><h1>⥥</h1><p class="note">————————————</p><p class="note"><sup>1</sup> de préférence déconnecté du réseau.</p><p class="note"><sup>2</sup> offre limitée à un crédit par individu et pour un compte créé en 2014...la communication de votre nom est nécessaire seulement pour éviter les doublons.</p><p class="note">&nbsp;&nbsp;&nbsp;La base de donnée qui lie votre nom à votre ID n\'est pas accessible en ligne. Nous pouvons effacer ce lien si vous nous remboursez cet euro.</p></div><div class="page aa"><h1>2- Provisionnez</h1><p>Nous n\'utilisons que les virements <a href="http://fr.wikipedia.org/wiki/Single_Euro_Payments_Area">SEPA</a> (€)</p><p>Effectuez un virement<sup>1</sup> de la somme que vous désirez sur le compte bancaire:</p><p><b>CUP-FOUNDATION</b> <i>BIC</i>: CMCIFR2A <i>IBAN</i>: <b>FR76 1027 8022 3300 0202 8350 157</b> <i>ID</i>: <a class="id" href="dsds">IbankVBixRIm</a></p><p>N\'oubliez pas d\'indiquer en message l\'ID de votre compte à créditer</p><p>Ce compte sera provisioné sous moins de 24 heures</p><p>————</p><p>Aucune commission n\'est retenue, ni à l\'achat, ni à la vente</p><p>Les comptes ne sont pas rémunérés et jamais débiteurs</p><p>Indiquez nous si vous désirez des ⊔<sup>2</sup> à la place des €</p><h1>⥥</h1><p class="note">————————————</p><p class="note"><sup>1</sup> Vous pouvez aussi fournir un de vos ID à vos débiteurs pour régler directement sur ce compte.</p><p class="note"><sup>2</sup> La conversion € vers ⊔ ou de ⊔ vers € est soumise à une TVA de 3,5% reversée au Trésor-Public. Le taux de change nominal est consultable <a href="df">ici</a></p></div><div class="page bb"><h1>3- Echangez</h1><p>Tous les échanges sont possibles tant que le solde reste positif</p><p>Echangez entre vos comptes, sans limite</p><p>Echangez aussi avec des tiers qui possèdent un ID<sup>1</sup></p><p>Achetez des biens immatériels culturels et vendez vos créations numériques, en ⊔<sup>2</sup></p><p>Consultez à tout moment vos soldes et opérations sur <a href="hh">Internet</a></p><p>————</p><p>Si vous désirez vous retirer, transmettez nous votre IBAN et créditez du solde l\'ID <a class="id" href="dsddd">IbankVBixRIm</a></p> <p>Le virement SEPA sera effectué sous 24 heures</p><h1>⥥</h1><p class="note">————————————</p><p class="note"><sup>1</sup> insitez vos contacts à créer leur propre ID. Nous ne faisons aucune publicité.</p><p class="note"><sup>2</sup> Les échanges directs en ⊔ entre personnes ne sont pas autorisés, seulement avec une <b>i-Bank</b>.</p><p class="note"><sup>3</sup> Nous proposerons en 2015 de chèques électronique et de billets électronique à usage unique.</p></div><div class="page cc"><h1>Une question ?</h1><h1>⥥</h1><p>Pas d\'hésitation, contactez nous !</p><p>————————</p><h2>&nbsp;</h2></div><div class="page foot"><p>Contact: <a href="mailto:laurent.fournier@cupfoundation.net">⊔Foundation</a>&nbsp;&nbsp;&nbsp;<i>SIREN:</i> 399 661 602 00025&nbsp;&nbsp;&nbsp;<i>Tel:</i> 06 19 29 14 85</p><p>&nbsp;</p></div><h1 class="header"><a class="header" href="http://cupfoundation.net">⊔</a></h1>'
    return '<?xml version="1.0" encoding="utf8"?>\n<html>%s%s<meta charset="utf-8"/>%s</html>' % (favicon(), style(), o)

def membership():
    "_"
    o = """<div class="page dd"><h1>Adhérez à l\'association <br/>dès 2014 !</h1>
<p>L\'association <a href="http://eurofranc.fr">Eurofranc</a> soutient la mise en oeuvre d`un moyen de <b>paiement numérique citoyen</b></p>
<p>dont la masse monétaire créée en €f est équitablement répartie sur <b>50 Millions</b> de personnes vivant en France.</p> 
<p>Le premier versement prévu en <b>Janvier 2015</b>, atteindra un montant de <b>150€f/mois</b> fin 2015</p>
<p>L\'association forme une <b>autorité indépendante</b> et auditable, chargée de la sécurité informatique</p>
<p>Le montant de l\'adhésion est minimum de 10€ pour les personnes et de 100€ pour les organisations</p>
<p>50%%<sup>2</sup> de l\'adhésion est converti en €f crédités sur un compte numérique de l'adhérant, utilisable dès 2015,<p>
<p>le reste de est dévolu aux frais de fonctionnement de l\'association</p>
<h1>⥥</h1>
<p class="note">————————————</p>
<p class="note"><sup>1</sup>Les comptes de l\'association sont visibles sur Internet</p>
<p class="note"><sup>2</sup>Le bureau de l\'association peut décider par assemblée générale de modifier le taux de cette répartition, mais sans effet rétroactif</p>
</div>
<div class="page aa"><h1>2- Provisionnez</h1><p>Nous n\'utilisons que les virements <a href="http://fr.wikipedia.org/wiki/Single_Euro_Payments_Area">SEPA</a> (€)</p><p>Effectuez un virement<sup>1</sup> de la somme que vous désirez sur le compte bancaire:</p><p><b>CUP-FOUNDATION</b> <i>BIC</i>: CMCIFR2A <i>IBAN</i>: <b>FR76 1027 8022 3300 0202 8350 157</b> <i>ID</i>: <a class="id" href="dsds">IbankVBixRIm</a></p><p>N\'oubliez pas d\'indiquer en message l\'ID de votre compte à créditer</p><p>Ce compte sera provisioné sous moins de 24 heures</p><p>————</p><p>Aucune commission n\'est retenue, ni à l\'achat, ni à la vente</p><p>Les comptes ne sont pas rémunérés et jamais débiteurs</p>
<h1>⥥</h1><p class="note">————————————</p><p class="note"><sup>1</sup> Vous pouvez aussi fournir un de vos ID à vos débiteurs pour régler directement sur ce compte.</p></div><div class="page bb"><h1>3- Echangez</h1><p>Tous les échanges sont possibles tant que le solde reste positif</p><p>Echangez entre vos comptes, sans limite</p><p>Echangez aussi avec des tiers qui possèdent un ID<sup>1</sup></p>
<p>Consultez à tout moment vos soldes et opérations sur <a href="hh">Internet</a></p><p>————</p><p>Si vous désirez vous retirer, transmettez nous votre IBAN et créditez du solde l\'ID <a class="id" href="dsddd">IbankVBixRIm</a></p> <p>Le virement SEPA sera effectué sous 24 heures</p><h1>⥥</h1><p class="note">————————————</p><p class="note"><sup>1</sup> insitez vos contacts à créer leur propre ID. Nous ne faisons aucune publicité.</p></div>
<div class="page cc"><h1>Une question ?</h1><h1>⥥</h1><p>Pas d\'hésitation, contactez nous !</p><p>————————</p><h2>&nbsp;</h2></div><div class="page foot"><p>Contact: <a href="mailto:laurent.fournier@cupfoundation.net">⊔Foundation</a>&nbsp;&nbsp;&nbsp;<i>SIREN:</i> 399 661 602 00025&nbsp;&nbsp;&nbsp;<i>Tel:</i> 06 19 29 14 85</p><p>&nbsp;</p></div><h1 class="header"><a class="header" href="http://eurofranc.fr"><img src="%s" width="100"/></a></h1>""" % get_image('www/logo.png')
    return '<?xml version="1.0" encoding="utf8"?>\n<html>%s%s<meta charset="utf-8"/>%s</html>' % (favicon(), style(), o)

def favicon_ppc():
    "_"
    return '<link rel="shortcut icon" type="www/image/png" href="data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAFAAAABQCAIAAAABc2X6AAAABmJLR0QA/wD/AP+gvaeTAAAAoklEQVR4nO3csQ0CMRAAQR6R0wk1URo1UYnpgA4M0iNA65n0kltdankbYxxWcvz1At8muE5wneA6wXWn+fhyO0+m9+vjo8u8a89Wy11YcJ3gOsF1gusE1wmuE1wnuE5wneA6wXWC6wTXCa4TXCe4TnCd4DrBdYLrBNcJrhNcJ7juxYv4ufnL9P+03IUF1wmuE1wnuG7zy0Oc4DrBdYLrBNc9AUj0DSD4QMJ7AAAAAElFTkSuQmCC"/>'

def favicon():
    "_"
    return '<link rel="shortcut icon" type="www/image/png" href="data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAMAAAAoLQ9TAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAgY0hSTQAAeiYAAICEAAD6AAAAgOgAAHUwAADqYAAAOpgAABdwnLpRPAAAAXFQTFRF/wCA/wOC/wF//wB5/wB3/wB+/wKB/wqD/0Cg/1+v/z+g/wqF/wWC/wSC/1ms/+Px//////7///v9/2e0/wB0/wR4/wB1/wB8/wCB/wB4/2qz/+32/7fb/7nc//r9/zmb/xiL/4XC/5bL/y6X/wB7/yOP//L4/8fj/xaL/x+P/xKH/9Lp/+Ty/0ul/4LB//3+/ziZ/wmF/7ze/wJ//wB6/6/X//b7//j8//X6/w+I/zOZ/9/v/9rs/0mk/0ym/0um/02m/1ut/222/9Xq/1Kp/weE/wB//wB9/2Gw//D3/+by/ofD/onE/4zG/4fD/wp9/xB//7jZ/wBw/wOB/4/H/c/m/M3l/77f/wuF/7rc/wSD/wBx/3W3/ziV/wBu/wN7/wF6/xOG//3//7Xa/x2N/+v1/9Lo/ySS/yuW/1Co/7rd/1ys//H4/8Lh/8Ph/3y+/3a7/2az/wGB/06m/9zu//z+/wBv/wR7/weB/zmd/1SqcikTHwAAAAFiS0dEEJWyDSwAAAAJcEhZcwAACxMAAAsTAQCanBgAAADvSURBVBjTY2AAAkYmZhYWZlYGGGBjZufg5OTiZuDhZYPw+fgFBIUEhEVExcQlgOolpQQEpGVk5eQVFJWUxRnYVFTVBNQ1JJk1tbQFdHSZGXiZ9QT0DZi5DcUVBIxYjBkYTEwF9PXNhMzNzSz0BfgtWRlYrawFbGzt7B0cnQScXVzdGNw9PAW8vH18/fwDBAKDghkYVEIsBIRCw5zDIzQEIlWAAlHRMQKCsXHxCZKJScnMQAE21pRUgbR0cfeMTPMskADQYdkCAjm5eQL5BYXiRRCnF5cICJYKeJSVS8A8V1FZ5aLMxssI8y7Y+yYQNgBQWiTEKkSv3QAAACV0RVh0ZGF0ZTpjcmVhdGUAMjAxNC0wNS0yNlQxMDozMDoxMCswMjowMP2x9zQAAAAldEVYdGRhdGU6bW9kaWZ5ADIwMTQtMDUtMjZUMTA6MzA6MTArMDI6MDCM7E+IAAAAAElFTkSuQmCC"/>'

def header():
    "_"
    o = '<a href="./"><img title="Enfin un moyen de paiement numérique, simple, gratuit et sécurisé !" src="%s"/></a>\n' % get_image('www/header.png')
    return o + '<p class="alpha" title="still in security test phase!">Beta</p>'

def header():
    "_"
    o = '<a href="./"><img title="Eurofranc 2015 pour l\'économie réelle !" src="%s" width="100"/></a>\n' % (get_image('www/logo.png'))
    #o = '<h1>Eurofranc 2015 pour l\'économie réelle !</h1>'
    return o 

def get_image(img):
    "_"
    here = os.path.dirname(os.path.abspath(__file__))
    return 'data:image/png;base64,%s' % base64.b64encode(open('%s/%s' % (here, img), 'rb').read()).decode('ascii')

def print_image(img):
    "_"
    here = os.path.dirname(os.path.abspath(__file__))
    print ('data:image/png;base64,%s' % base64.b64encode(open('%s/%s' % (here, img), 'rb').read()).decode('ascii'))

def footer(dg=''):
    "_"
    dg = ' %s' % dg if dg else ''
    here = os.path.dirname(os.path.abspath(__file__))
    hh = '<a href="host.png">Host</a> - ' if os.path.isfile(here + '/host.png') else ''
    return '<footer>%sContact: <a href="mailto:%s">%s</a>%s<br/><a href="http://cupfoundation.net">⊔FOUNDATION</a> is registered in Toulouse/France SIREN: 399 661 602 00025</footer>' % (hh, __email__, __email__, dg)

def report(d, cm):
    "_"
    un = '<euro>&thinsp;€</euro>'
    du, dt, dc, bal, o = d['pub'], d['trx'], d['crt'], 0, '<table width="100%"><tr><th width="30"></th><th width="82">Date</th><th width="148">Réf.</th><th>Msg</th><th width="60">Débit</th><th width="60">Crédit</th></tr>'
    z, root, dar, n , tmp = b'%'+cm, dc[b'_'], None, 0, []
    if z in dc: 
        dar, bal = dc[z][:4], b2s(dc[z][4:8], 4)
        o += '<tr><th></th><th>%s</th><th colspan="3">Ancien solde</th><th></th><th class="num">%s&nbsp;€</th></tr>' % (datdecode(dar), (bal/100))
    for t in dt.keys():
        if len(t) == 13 and (dar==None or is_after(t[:4], dar)):
            src, cry, dst, prc = t[4:], dt[t][:1], dt[t][1:10], b2i(dt[t][10:13])
            if cm in (dst, src) and cry == b'A':
                if src == cm: 
                    one, t1, t2, bal = dst, '<td class="num" title="%s"><b><a href="./%s">%7.2f%s</a></b></td>' % (btob64(t), btob64(t), prc/100, un), '<td></td>', bal-prc 
                else: 
                    one, t1, t2, bal = src, '<td></td>', '<td class="num" title="%s"><b><a href="/%s">%7.2f%s</a></b></td>' % (btob64(t), btob64(t), prc/100, un), bal+prc
                typ = get_type(d, one)
                desc = dt[t][13:-132].decode('utf8')
                tmp.append((t[:4], '<td class="num">%s</td><td><a class="mono" href="%s" title="%s"><img src="%s"/>&thinsp;%s&#8203;%s&#8203;%s</a></td><td>%s</td>%s%s</tr>' % (datdecode(t[:4]), btob64(one), btob64(one), get_image('www/%s32.png' % typ), btob64(one)[:4], btob64(one)[4:8], btob64(one)[8:], desc, t1, t2)))
    size = len(tmp)
    for i, (d, x) in enumerate(sorted(tmp, reverse=True)): o += '<tr><td class="num"><b>%04d</b></td>' % (size-i) + x
    o += '<tr><th colspan="2">%s</th><th colspan="2"><b>Nouveau solde</b></th>' % datdecode(datencode())
    o += '<th></th><th class="num"><b>%7.2f%s</b></th></tr>' % (-bal/100, un) if bal<0 else '<th class="num"><b>%7.2f%s</b></th><th></th></tr>' % (bal/100, un)
    return o + '</table>\n', bal

def reportC(d, cm):
    "_"
    o = '<table width="100%"><tr><th width="30"></th><th width="82">Date</th><th width="148">Réf.</th><th width="20"></th><th>Message</th></tr>'
    dt, root, dar, n , tmp = d['trx'], d['crt'][b'_'], None, 0, []
    for t in dt.keys():
        if len(t) == 13 and (dar==None or is_after(t[:4], dar)):
            src, cry, dst = t[4:], dt[t][:1], dt[t][1:10]
            if cm in (dst, src) and cry == b'C':
                one = dst if src == cm else src
                dir = '⇐' if src == cm else '⇒'
                typ = get_type(d, one)
                desc = dt[t][10:-132].decode('utf8')
                tmp.append((t[:4], '<td class="num">%s</td><td><a class="mono" href="%s" title="%s"><img src="%s"/>&thinsp;%s&#8203;%s&#8203;%s</a></td><td><b class="biggreen">%s</b></td><td>%s</td></tr>' % (datdecode(t[:4]), btob64(one), btob64(one), get_image('www/%s32.png' % typ), btob64(one)[:4], btob64(one)[4:8], btob64(one)[8:], dir, desc)))
    if len(tmp) == 0: return ''
    for i, (d, x) in enumerate(sorted(tmp, reverse=True)): o += '<tr><td class="num"><b>%04d</b></td>' % (len(tmp)-i) + x
    return o + '</table>\n'

def reportCRT(d, cm):
    "_"
    un = '<euro>&thinsp;€</euro>'
    du, dt, dc, bal, o = d['pub'], d['trx'], d['crt'], 0, '<table width="100%"><tr><th width="30"></th><th width="82">Expire</th><th width="148">Réf.</th><th>Certificat</th></tr>'
    root, dar, n , tmp = dc[b'_'], None, 0, []
    for c in dc.keys():
        if len(c) > 1 and len(dc[c]) == 157 and cm == dc[c][4:13]:
            typ = get_type(d, c)
            year, hh = b2i(dc[c][13:15]), btob64(dc[c][15:25])
            tmp.append((dc[c][:4], '<td class="num">%s</td><td><a class="mono" href="%s" title="%s"><img src="%s"/>&thinsp;%s&#8203;%s&#8203;%s</a></td><td>%s %s</td></tr>' % (datdecode(dc[c][:4]), btob64(c), btob64(c), get_image('www/%s32.png' % typ), btob64(c)[:4], btob64(c)[4:8], btob64(c)[8:], year, hh )))
        elif len(c) > 1 and cm == root:
            if len(dc[c]) == 144:
                typ = get_type(d, c)
                dbt = b2i(dc[c][4:12])
                tmp.append((dc[c][:4], '<td class="num">%s</td><td><a class="mono" href="%s" title="%s"><img src="%s"/>&thinsp;%s&#8203;%s&#8203;%s</a></td><td>%s%s</td></tr>' % (datdecode(dc[c][:4]), btob64(c), btob64(c), get_image('www/%s32.png' % typ), btob64(c)[:4], btob64(c)[4:8], btob64(c)[8:], dbt, un)))
            elif len(dc[c]) == 136:
                typ = get_type(d, c)
                tmp.append((dc[c][:4], '<td class="num">%s</td><td><a class="mono" href="%s" title="%s"><img src="%s"/>&thinsp;%s&#8203;%s&#8203;%s</a></td><td>MAIRIE</td></tr>' % (datdecode(dc[c][:4]), btob64(c), btob64(c), get_image('www/%s32.png' % typ), btob64(c)[:4], btob64(c)[4:8], btob64(c)[8:])))
    if len(tmp) == 0: return ''
    for i, (d, x) in enumerate(sorted(tmp, reverse=True)): o += '<tr><td class="num"><b>%04d</b></td>' % (len(tmp)-i) + x
    return o + '</table>\n'

def report_cup(d, cm):
    "_"
    du, dt, dc, di, bal, o = d['pub'], d['trx'], d['crt'], d['igs'], 0, '<table><tr><th colspan="2">Date</th><th>Type</th><th>IG</th><th>Référence</th><th>Débit</th><th>Crédit</th></tr>'
    z, root, n , tmp = b'%'+cm, dc[b'_'], 0, []
    typ, empty = '<td title="particulier ou commerçant">part.</td>', '<td></td>'
    for i in di.keys(): # created IG
        if di[i][:9] == cm and len(i) == 10:
            url = d['igs'][b'%'+i]
            dat, prc = datdecode(di[i][9:13]), income(di, i)
            t1, bal = '<td class="num">%7d&nbsp;⊔</td>' % prc, bal+prc 
            tmp.append((di[i][9:13], '<td class="num">%s</td>%s<td><a href="%s" class="mono">%s</a></td><td class="mono">%s</td>%s%s</tr>' % (dat, typ, url.decode('utf8'), btob64(i), btob64(cm), empty, t1)))
    for t in dt.keys(): # bank funding
        if len(t) == 13:
            src, cry, dst, prc = t[4:], dt[t][:1], dt[t][1:10], b2i(dt[t][10:13])
            if cm == dst and cry == b'U':
                dat = datdecode(t[:4])
                t1, bal = '<td class="num">%7d&nbsp;⊔</td>' % prc, bal+prc 
                tmp.append((t[:4], '<td class="num">%s</td>%s<td>Retrait</td><td><a class="mono" href="?%s">%s</a></td>%s%s</tr>' % (dat, typ, btob64(src), btob64(src), empty, t1)))
    for t in dt.keys(): # bank deposit
        if len(t) == 13:
            src, cry, dst, prc = t[4:], dt[t][:1], dt[t][1:10], b2i(dt[t][10:13])
            if cm == src and cry == b'U':
                dat = datdecode(t[:4])
                t1, bal = '<td class="num">%7d&nbsp;⊔</td>' % prc, bal-prc 
                tmp.append((t[:4], '<td class="num">%s</td>%s<td>Financement</td><td><a class="mono" href="?%s">%s</a></td>%s%s</tr>' % (dat, typ, btob64(dst), btob64(dst), t1, empty)))
    for t in dt.keys(): # bought IG
        if len(t) == 14 and cm == dt[t][:9]:
            src, dst, prc, ig = dt[t][:9], dt[t][:9], price(di, t[4:], b2i(t[:4])), t[4:]
            t1, bal = '<td class="num">%7d&nbsp;⊔</td>' % prc, bal-prc 
            auth, dat = di[ig][:9], datdecode(dt[t][9:13])
            tmp.append((dt[t][9:13], '<td class="num">%s</td>%s<td class="mono">%s</td><td><a class="mono" href="?%s">%s</a></td>%s%s</tr>' % (dat, typ, btob64(ig), btob64(auth), btob64(auth), t1, empty)))
    for i, (d, x) in enumerate(sorted(tmp)): o += '<tr><td class="num">%03d</td>' % (i+1) + x
    o += '<tr><th colspan="2">%s</th><th colspan="3"><b>Nouveau solde</b></th>' % datdecode(datencode())
    if bal < 0:
        o += '<th></th><th class="num"><b>%7d&nbsp;⊔</b></th></tr>' % (-bal)
    else:
        o += '<th class="num"><b>%7d&nbsp;⊔</b></th><th></th></tr>' % (bal)
    return o + '</table>\n', bal

def report_ig(d, cm):
    "_"
    di, o, found = d['igs'], '<table><tr><th>IG</th><th>Date</th><th>F-prix</th><th>Nb</th></tr>', False
    for i in di.keys():
        if di[i][:9] == cm and len(i) == 10:
            url = d['igs'][b'%'+i]
            found, src, dat = True, btob64(di[i][:9]), datdecode(di[i][9:13])
            xi, p1, pf = valdecode(di[i][13:20])
            o += '<tr><td><a href="%s" class="mono">%s</a></td><td class="num">%s</td><td class="num">%d/%d&nbsp;⊔ (%d%%)</td><td class="num">%s</td></tr>' % (url.decode('utf8'), btob64(i), dat, p1, pf, xi, (len(di[i])-152)//9)
    return o + '</table>' if found else ''

def blc(d, cm, cry=b'A'):
    "balance for both   or cup"
    dt, di, bal = d['trx'], d['igs'], 0
    if cry == b'U':
        for t in filter(lambda i:di[i][:9]==cm, di.keys()): bal += income(di, t) # created IG (+)
    for t in dt.keys(): 
        if len(t) == 14 and cry == b'U' and cm == dt[t][:9]: bal -= price(di, t[4:], b2i(t[:4])) # bought IG (-)
        elif len(t) == 13 and dt[t][:1] == cry:
            if cm == dt[t][1:10]: bal += b2i(dt[t][10:13]) # bank funding (+)
            if cm == t[4:]:       bal -= b2i(dt[t][10:13]) # bank deposit (-)
    return bal

def blc_old(d, cm):
    "_"
    du, dt, dc, bal = d['pub'], d['trx'], d['crt'], 0
    z, root, dar, k = b'%'+cm, dc[b'_'], None, ecdsa()
    #k.pt = Point(c521, b2i(du[root][:66]), b2i(du[root][66:]+root))
    #if z in dc and k.verify(dc[z][8:], cm + dc[z][:8]): dar, bal = dc[z][:4], b2s(dc[z][4:8], 4)
    if z in dc: dar, bal = dc[z][:4], b2s(dc[z][4:8], 4)
    for t in dt.keys():
        if (len(t) == 13) and dt[t][:1] == b'A' and (dar==None or is_after(t[:4], dar)):
            src, cry, dst, prc = t[4:], dt[t][:1], dt[t][1:10], b2i(dt[t][10:13])
            #k.pt = Point(c521, b2i(du[src][:66]), b2i(du[src][66:]+src))
            if (src == cm or dst == cm):# and k.verify(dt[t][12:], t + dt[t][:12]):
                if src == cm: bal -= prc
                if dst == cm: bal += prc 
    return bal

def cleantr():
    "_"
    du, dt, dc, k = dbm.open(__base__+'pub'), dbm.open(__base__+'trx', 'c'), dbm.open(__base__+'crt'), ecdsa()
    for u in du.keys(): 
        z, root, dar = b'%'+u, dc[b'_'], None
        k.pt = Point(c521, b2i(du[root][:66]), b2i(du[root][66:]+root))
        if z in dc and k.verify(dc[z][8:], u + dc[z][:8]): dar, bal = dc[z][:4], b2s(dc[z][4:8], 4)
        for t in dt.keys():
            if dar and is_after(dar, t[:4]): del dt[t]
    du.close(), dt.close(), dc.close()

##### WEB APP #####

def peers_req(host='localhost'):
    "_"
    co, serv = http.client.HTTPConnection(host), '/' #+ __app__
    co.request('POST', serv, urllib.parse.quote('PEERS'))
    return eval(co.getresponse().read().decode('utf8'))    

def req(host='localhost', data=''):
    "_"
    co, serv = http.client.HTTPConnection(host), '/' #+ __app__
    co.request('POST', serv, urllib.parse.quote(data))
    return eval(co.getresponse().read())    

def digest_req(host='localhost'):
    "_"
    co, serv = http.client.HTTPConnection(host), '/' #+ __app__
    co.request('POST', serv, urllib.parse.quote('DIGEST'))
    return co.getresponse().read()    

def reg(value):
    " function attribute is a way to access matching group in one line test "
    reg.v = value
    return value

def init_dbs(dbs, port):
    "_"
    di = '/%s/%s_%s' % (__app__, __app__, port)
    if not os.path.exists(di): os.makedirs(di)
    for dbn in dbs:
        db = '%s/%s' % (di, dbn)
        if not (os.path.isfile(db) or os.path.isfile(db+'.db')):
            d = dbm.open(db, 'c')
            d.close()
            os.chmod(db, 511)
    return {b:dbm.open('%s/%s' % (di, b), 'c') for b in dbs}

def update_peers(env, d, li):
    "_"
    now = '%s' % datetime.datetime.now()
    #for p in filter(lambda i:i != env['HTTP_HOST'] and bytes(i, 'utf8') not in d, li): d[p] = now[:19]
    for p in li:
        if p != env['HTTP_HOST'] and bytes(p, 'utf8') not in d: d[p] = now[:19]
    return 'Peers: %s\nDigest: %s' % ({x.decode('utf8'):d[x].decode('utf8') for x in d.keys()}, rdigest(env['SERVER_PORT']))

def update_db(db, d, li):
    "_"
    if li and db == 'crt' and b'_' in d[db] and d[db][b'_'] != li[b'_']: return # manage root first
    for x in li:
        if x not in d[db]: d[db][x] = li[x]

def hmerge(d, port, tab):
    "_"
    trx, crt, pub, k = {}, {}, {}, ecdsa()
    for p in tab: 
        trx.update(req(p.decode('utf8'), 'TRX%s' % {x: d['trx'][x] for x in d['trx'].keys()}))
        crt.update(req(p.decode('utf8'), 'CRT%s' % {x: d['crt'][x] for x in d['crt'].keys()}))
        pub.update(req(p.decode('utf8'), 'PUB%s' % {x: d['pub'][x] for x in d['pub'].keys()}))
    if b'_' in d['crt'] and b'_' in crt: assert crt[b'_'] == d['crt'][b'_']
    if not b'_' in d['crt']: d['crt'][b'_'] = crt[b'_']
    root = d['crt'][b'_']
    for u in pub: 
        if len(u) !=9 and len(pub[u]) != 123: del pub[u]
        if u not in d['pub']: d['pub'][u] = pub[u]
    for t in trx:
        if len(t) !=13 and len(trx[t]) != 144: del trx[t]
        src = t[4:]
        k.pt = Point(c521, b2i(d['pub'][src][:66]), b2i(d['pub'][src][66:]+src))
        if not k.verify(trx[t][12:], t + trx[t][:12]): del trx[t]
        if t not in d['trx']: d['trx'][t] = trx[t]
    for c in crt:
        k.pt = Point(c521, b2i(d['pub'][root][:66]), b2i(d['pub'][root][66:]+root))
        if len(c) == 9: # bank certificat
            if k.verify(crt[c][12:], c + crt[c][:12]) and c not in d['crt']: d['crt'][c] = crt[c]
        elif len(c) == 10: # cut
            if k.verify(crt[c][8:], c[1:] + crt[c][:8]) and c not in d['crt']: d['crt'][c] = crt[c]
    wdigest(d, port)

def app_update(host):
    "_"
    cd = 'cd %s; git pull origin' % os.path.dirname(os.path.abspath(__file__))
    out, err = subprocess.Popen((cd), shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE).communicate()
    o = '<html><pre>Application Update...\n'
    o += '%s\n' % err.decode('utf8') if err else 'Message:%s\n' % out.decode('utf8')
    o += '</pre><br/><a href="/">Reload the new version</a>'
    return o + footer() + '</html>'

def capture_id(d, arg):
    "_"
    res = [btob64(u) for u in filter(lambda i:re.match(arg, btob64(i)), d['pub'].keys())]
    if len(res) == 1: return res[0]
    return ''

def capture_ig(d, arg):
    "_"
    res = [ u for u in filter(lambda i:len(i) == 10 and re.match(arg, btob64(i)), d['igs'].keys())]
    if len(res) == 1: return btob64(res[0])
    return ''

def jscript():
    """window.onload=main;
var BUYERS = 0;
var PINF = 1000;
function main() {
 document.getElementById('svg1').addEventListener('mousedown', mousefunc, false);
 document.documentElement.addEventListener('keydown', keyfunc, false);
 draw(BUYERS);
}
function mousefunc(evt) {
  var p = evt.clientX-37;
  BUYERS = Math.floor(p*PINF/700);
  if (p>0 && p<700) { draw(BUYERS); }
}
function keyfunc(e) {
  if (e.type == 'keydown') {
    if (e.keyCode == 39) { BUYERS+=1; draw(BUYERS);}
    if (e.keyCode == 37) { if (BUYERS > 0 ) BUYERS-=1; draw(BUYERS);}
  }
}
function draw (b) {
  var s = new String(document.location);
  var p1 = document.getElementById("p1").value;
  var pf = document.getElementById("pf").value;
  PINF = parseInt(pf);
  var s = new String(document.location);
  var aj = new ajax_get(s + '&i=' + b, function(res){
    var myRegexp = /(\d+)\*(\d+)⊔ \+ (\d+)\*(\d+)⊔ = (\d+)⊔$/;
    var m = myRegexp.exec(res);
    var xpos = parseInt(b*700/parseInt(pf))+30;
    document.getElementById("path1").setAttribute('d', "m" + xpos + ",10l0,300");
    var t0 = document.getElementById('t0');var t1 = document.getElementById('t1');var t2 = document.getElementById('t2');var t3 = document.getElementById('t3');var t4 = document.getElementById('t4');
    t0.setAttribute('x', xpos+2);t1.setAttribute('x', xpos+2);t2.setAttribute('x', xpos+2);t3.setAttribute('x', xpos+2);t4.setAttribute('x', xpos+2);
    var nbas = 's';
    var nba = parseInt(m[1])+parseInt(m[3]);
    if (nba == 1) nbas = '';
    t0.textContent = nba + ' acheteur' + nbas;
    t1.textContent = 'Revenu: ' + m[5] +  '⊔';
    var prs = 's';var sus = 's';
    if (m[1] == 1) prs = '';
    if (m[3] == 1) sus = '';
    if (m[1] == 0) t2.textContent = ''; else t2.textContent = 'Prix '+ m[1] +' premier' + prs + ' : ' + m[2] + '⊔';
    if (m[3] == 0) t3.textContent = ''; else t3.textContent = 'Prix '+ m[3] +' suivant' + sus + ' : ' + m[4] + '⊔';
    t4.textContent = res;
    var c1 = document.getElementById('c1');
    var c2 = document.getElementById('c2');
    c1.setAttribute('cx', xpos);
    c2.setAttribute('cx', xpos);
    c3.setAttribute('cx', xpos);
    c1.setAttribute('cy', 310 - m[5]*300/pf);
    if (m[1] == 0) c2.setAttribute('cy', 10 + 300*(1-m[4]/p1)); else c2.setAttribute('cy', 10 + 300*(1-m[2]/p1));    
    if (m[3] == 0) c3.setAttribute('cy', 10 + 300*(1-m[2]/p1)); else c3.setAttribute('cy', 10 + 300*(1-m[4]/p1));    
  });
  aj.doGet();
};
function ajax_get(url, cb) {
  var req = new XMLHttpRequest();
  req.onreadystatechange = processRequest;
  function processRequest () {
    if (req.readyState == 4) {
      if (req.status == 200 || req.status == 0) { if (cb) { cb(req.responseText); }
      } //else { alert('Error Get status:'+ req.status);}
    }
  }
  this.doGet = function() { req.open('GET', url); req.send(null);}
};"""
    return jscript.__doc__

def simu(d, env, p1, pi, graph=False):
    "_"
    o = '<?xml version="1.0" encoding="utf8"?>\n<html>\n'
    o += '<meta name="viewport" content="width=device-width, initial-scale=1"/>'
    o += favicon() + style_html(False) + header()
    if graph: o += '<script>' + jscript() + '</script>'
    o += '<p><form><table>'
    if graph:
        dp1, dpf = 'value="%s"' % p1, 'value="%s"' % pi
    else:
        dp1, dpf = 'placeholder="⊔"', 'placeholder="⊔"'
    o += '<tr><td>Prix initial</td><td><input id="p1" class="simu" pattern="[0-9]+" name="p" title="(⊔)" %s></td>' % dp1
    o += '<td>Revenu attendu</td><td><input id="pf" class="simu" pattern="[0-9]+" name="f" title="(⊔)" %s></td></tr>' % dpf
    o += '</table><input type="submit" value="Calculer"></form></p>'
    if graph:
        o += '<p class="note">Sélectionnez le nombre d\'acheteurs avec le pointeur ou avec les touches "gauche"/"droite"</p>\n'
    l1, l2, dx, dy = '', '', 30, 10
    if graph:
        o += '<svg %s id="svg1" width="100%%" height="320">\n' % (_SVGNS)
        o += '<rect x="%s" y="%s" width="800" height="300" style="stroke:gray;fill:none"/>\n' % (dx, dy) 
        o += '<path id="path1" d="m%s,%sl0,300" style="stroke:gray;stroke-width:1"/>\n' % (dx, dy)
        for i in range(5):
            if i == 1: sty = ' style="fill:blue"'
            elif i in (2, 3): sty = ' style="fill:red"'
            else: sty = ''
            o += '<text id="t%d" y="%d"%s></text>' % (i, 50 + 30*i, sty)
        for i in range(0, pi+pi//10, pi//100 if pi>=100 else 1):
            p, k = func_price(p1, pi, i)
            tau = (i+1-k)*(p+1) +k*p
            pr = tau/(i+1)
            l1 += 'L%s,%s' % (dx + i*700/pi, 300+dy - tau*300/pi)
            l2 += 'L%s,%s ' % (dx + int(i*700/pi), dy + int(300*(1-pr/p1)))
        o += '<path d="M%s" style="stroke:blue;stroke-width:1;fill:none;"/>\n<path d="M%s" style="stroke:red;stroke-width:1;fill:none;"/>\n' % (l1[1:], l2[1:])  
        o += '<text x="2" y="10" style="fill:red;font-size:10">%s⊔</text>' % p1
        o += '<text x="2" y="310" style="fill:red;font-size:10">0⊔</text>'
        o += '<text x="840" y="10" style="fill:blue;font-size:10">%s⊔</text>' % pi
        o += '<text x="840" y="310" style="fill:blue;font-size:10">0⊔</text>'
        o += '<circle id="c1" r="4" style="fill:blue"/><circle id="c2" r="4" style="fill:red"/><circle id="c3" r="4" style="fill:red"/>\n'  
        o += '</svg>\n'
    if graph:
        o += '<p>Nb*(Prix+1) + (N°acheteur-Nb)*Prix = Revenu auteur(s) [⊔]</p>\n'
    atrt = btob64(d['crt'][b'_'])[:5] if b'_' in d['crt'] else 'None'
    return o + footer('Authority: %s' % (atrt) ) + '</body></html>\n'

def bank(d, env):
    "_"
    o = '<?xml version="1.0" encoding="utf8"?>\n<html>\n'
    o += '<meta name="viewport" content="width=device-width, initial-scale=1"/>'
    o += favicon() + style_html() + '<body><div class="bg"></div>' + header()
    o += '<p class="msg" title="une offre par personne!"><a href="mailto:%s">Contactez nous,</a> nous offrons 1€ + 10⊔ sur tout compte créé avant le 01/09/2014 !</p>' % __email__
    bnk = get_random_ibank(d['crt'])
    o += '<h1>La première <b class="red">iBanque</b> offrant ce nouveau moyen de paiement</h1>'
    o += '<h1>Notre identifiant (ID):&nbsp;<b class="green"><b class="mono">%s</b></b></h1>' % bnk
    o += '<p>Créez un compte <a class="ppc">PingPong</a> sur votre téléphone portable (iPhone ou Android-Phone).</p><p>Le solde est initialement nul. Pour le créditer:<ul><li>demandez à vos débiteurs de vous rembourser sur votre compte <a class="ppc">PingPong</a> ou,'
    o += '<li>faites un virement SEPA vers notre <i>iBanque</i>: <br/>Nom: CUP-FOUNDATION<br/>BIC: CMCIFR2A <br/>IBAN: FR76 1027 8022 3300 0202 8350 157,<li>ajoutez votre ID en message de virement oubien envoyez-nous un <a href="mailto:%s">email</a> contenant votre ID associé à la référence du virement,<li>nous créditerons votre compte <a class="ppc">PingPong</a> dans la journée (7j/7) dès reception du virement,<li>aucune commission n\'est retenue mais le compte <a class="ppc">PingPong</a> n\'est pas rémunéré.</ul>' % __email__
    o += '<p>Inversement, à tout moment, vous pouvez récuperer toute somme de votre compte <a class="ppc">PingPong</a>,</p><ul><li>faites un paiement vers notre <i>iBanque</i> (ID <b class="mono">%s</b> ou scannez le QRcode) du montant à retirer,<li><a href="mailto:%s">envoyez nous</a> votre IBAN+BIC ainsi que l\'ID de votre compte,<li>dans la journée (7j/7), la somme sera tranférée par virement SEPA au crédit de votre compte bancaire,<li>vous pouvez aussi régler vos créanciers avec le compte <a class="ppc">PingPong</a>,<li>aucune commission n\'est retenue et vous pouvez consulter votre compte depuis n\'importe quel point connecté au Net.</ul><p>Vous pouvez aussi nous demander de convertir des € en ⊔ ou inversement des ⊔ en € au <a href="/rates">taux nominal du jour</a>. Nous ne prenons aucune commission, mais une taxe de 5%% est prélevée pour chaque conversion et le montant de cette taxe est reversée au <i>Trésor Public</i>.</p>' % (bnk, __email__)
    o += '<p class="note">Aucune personne autre que vous, muni du téléphone sur lequel vous avez créé un compte, ne peut payer depuis votre compte <a class="ppc">PingPong</a>.<br/>Strictement personne ne peut retrouver votre passphrase si vous la perdez.<br/>A la création de votre compte, pensez à générer un <b>i-chèque</b> vers notre <i>iBanque</i> (%s) du montant que vous estimez vous assurer et gardez le fichier dans un endroit sécurisé, autre que le téléphone.<br/>Si vous perdez ou vous faites voler votre téléphone ou si vous oubliez votre passphrase, <a href="mailto:%s">Envoyez nous</a> l\'ID d\'un nouveau compte créé.<br>Nous créditerons ce nouveau compte dès que vous aurez posté l\'<b>i-chèque</b> de réserve à l\'encaissement.<br/>L\'ancien compte ainsi vidé ne peut plus être débité. Pensez à avertir vos débiteurs du changement de compte car les sommes qui depasseraient le montant de l\'<b>i-chèque</b> de réserve sur le compte perdu ou qui surviendraient après l\'encaissement seraient non récupérables.</p>' % (bnk, __email__)
    o += '<p class="note">Pour maintenir la confidentialité de vos comptes, nous <i>iBanque</i> ne pouvons pas associer votre identité à l\'un ou à l\'ensemble de vos comptes. L\'utilisation de plusieurs comptes vous assure un anonymat de vos transactions. Cependant vos débiteurs peuvent vous demander cette association afin qu\'ils puissent prouver devant un tier du remboursement de leur dette à la bonne personne et que vous ne puissiez pas contester ne pas avoir été payé.</p>' 
    o += '<div class="qr" title="%s">%s</div>\n' % (bnk, QRCode(bnk, 2).svg(0, 0, 4))
    atrt = btob64(d['crt'][b'_'])[:5] if b'_' in d['crt'] else 'None'
    return o + footer('Authority: %s' % (atrt) ) + '</body></html>\n'

def get_type(d, cm):
    if cm == d['crt'][b'_']: return 'admin'
    if cm in d['crt']:
        if len(d['crt'][cm]) == 144: return 'bank'
        if len(d['crt'][cm]) == 136: return 'maire'
        if len(d['crt'][cm]) == 157: return 'userp'
    else: return 'user'

def index(d, env, cm64='', prc=0):
    "_"
    o, un = '<?xml version="1.0" encoding="utf8"?>\n<html>\n', '<euro>&thinsp;€</euro>'
    o += '<meta name="viewport" content="width=device-width, initial-scale=1"/>'
    o += favicon() + style_html(False) + '<body><div class="bg"></div>' + header()
    #o1 = '<a title="moins de 2000 lignes Python3!" href="?src">Téléchargez</a> et <a title="sur GitHub" href="https://github.com/pelinquin/pingpongcash">analysez</a> le code du client <i>pair-à-pair</i><br/>Installez un <a href="?install">serveur</a> <i>Linux</i> ou <a href="?ios">l\'application</a> <i>iOS</i>' 
    o1 = '<p><i>Consultez un compte</i><form method="post"><input class="txt" pattern="\S+" required="yes" name="cm" placeholder="...ID"/><input class="txt" pattern=".+" required="yes" name="alias" placeholder="...alias"/><input type="submit" value="ok"/></form></p>\n'
    alias = ''
    if 'HTTP_COOKIE' in env:
        for x in env['HTTP_COOKIE'].split(';'):
            t = x.split('=')
            if t[1] == cm64: alias = urllib.parse.unquote(t[0])
            cm = b64tob(bytes(t[1], 'ascii'))
            dt = debt(d, cm)
            typ = get_type(d, cm)
            alia = urllib.parse.unquote(t[0])
            o1 += '<p><a href="./%s" title="%s"><img src="%s"/> %s</a></p>' % (t[1], t[1], get_image('www/%s32.png' % typ), alia)
        o1 += '<p><form method="post"><input type="submit" name="rem" value="Effacer les cookies"/></form></p>\n'
    qrurl = 'http://eurofranc.fr' 
    cm = b64tob(bytes(cm64, 'ascii'))
    if cm in d['pub']: qrurl += '/' + cm64
    o += '<div class="qr" title="%s">%s</div>\n' % (qrurl, QRCode(qrurl, 2).svg(0, 0, 4))
    if cm in d['pub']:
        rpt, bal = report(d, cm)
        #rpt1, bal1 = report_cup(d, cm)
        rpt1, bal1 = '', 0
        dt = debt(d, cm)
        typ = get_type(d, cm)
        o += '<h1><br/><img src="%s"/> <b class="mono">%s</b><br/><b class="green">%s</b></h1>' % (get_image('www/%s32.png' % typ), cm64, alias)
        v = ' value="%7.2f€"' % (prc/100) if prc else '' 
        o += '<form method="post"><input type="hidden" name="cm" value="%s"/>' % cm64
        #o += '<input class="digit" name="prc" pattern="[0-9]{1,4}([\.\,][0-9]{2}|)\s*€?" placeholder="---,-- €f"%s/></form>' % v
        #dbt = debt(d, cm, b'U')
        dbt = debt(d, cm)
        if dbt: o += '<h1>Dette:&nbsp;<b class="green">%9d%s</b></h1>' % (dbt, un)   
        if cm in d['crt']:
            if len(d['crt'][cm]) == 157: o += '<p>Année de naissance:&nbsp;<b class="green">%s</b></p>' % b2i(d['crt'][cm][13:15])   
            o += '<p>Expire:&nbsp;<b class="green">%s</b><p>' % datdecode(d['crt'][cm][:4])
            auto = btob64(d['crt'][cm][4:13]) if len(d['crt'][cm]) == 157 else btob64(d['crt']['_'])
            autb = d['crt'][cm][4:13] if len(d['crt'][cm]) == 157 else d['crt']['_']
            typc = get_type(d, autb)
            o += '<p>Certifié: <a href="%s"><img src="%s"/>&nbsp;<b class="mono">%s</b></a></p>' % (auto, get_image('www/%s32.png' % typc), auto)   
        o += '<h1><img src="%s"/><big><big><b class="green">%7.2f%s</b></big></big></h1>' % (get_image('www/balance32.png'), bal/100, un) + rpt + reportC(d, cm) + reportCRT(d, cm)
        da = btob64(cm) + ':%d' % prc if prc else ''
        #o += report_ig(d, cm)
        #o += '<p class="note">Découvrez notre <a href="?bank">iBanque</a> pour mieux profiter de ce moyen de paiement</p>'
    else:
        o += o1
    #o += '<p>%s</p>' % (env['HTTP_COOKIE'] if 'HTTP_COOKIE' in env else 'NONE')
    atrt = btob64(d['crt'][b'_'])[:5] if b'_' in d['crt'] else 'None'
    return o + footer('%s %s %s' % (rdigest(env['SERVER_PORT']), stat(d), atrt)) + '</body></html>\n'

def stat(d):
    "_"
    return '[%d:%d:%d:%d]' % (len(d['pub']), len(d['crt']), len(d['igs']), len(d['trx']))

def dashboard(d, env):
    "_"
    o = '<?xml version="1.0" encoding="utf8"?>\n<html>\n'
    o += '<meta name="viewport" content="width=device-width, initial-scale=1"/>'
    o += favicon() + style_html() + '<body><div class="bg"></div>' + header()
    o += '<table><tr><th>Compte</th><th>Solde&nbsp;€</th><th>Solde&nbsp;⊔</th><th>Dette</th></tr>'
    for u in d['pub'].keys():
        o += '<tr><td><a class="mono" href="./?%s">%s</a></td><td class="num">%7.2f&nbsp;€</td><td class="num">%9d&nbsp;⊔</td><td class="num">%9d</td></tr> ' % (btob64(u), btob64(u), blc(d, u)/100, blc(d, u, b'U'), debt(d, u) ) 
    o += '</table>'
    o += '<table><tr><th>Certificat</th><th>Date</th><th>Dette</th></tr>'
    for c in d['crt'].keys():
        if len(c) == 9 and len(d['crt'][c]) == 144:
            dat, dbt = datdecode(d['crt'][c][:4]), b2i(d['crt'][c][4:12])
            o += '<tr><td class="mono">%s</td><td class="num">%s</td><td class="num">%9d&nbsp;€</td></tr>' % (btob64(c), dat, dbt)
        elif len(c) == 1:
            o += '<tr><td class="mono">%s</td><td colspan="2">Autorité</td></tr>' % btob64(d['crt'][c])
        elif len(c) == 9 and len(d['crt'][c]) == 157:
            o += '<tr><td class="mono">%s</td><td class="num">%s</td><td>citizen</td></tr>' % (btob64(c), datdecode(d['crt'][c][:4]))
        else:
            o += '<tr><td class="mono">%s</td><td class="num">%s</td><td>maire</td></tr>' % (btob64(c), datdecode(d['crt'][c][:4]))
    o += '</table>'
    o += '<table><tr><th>IG</th><th>Auteur</th><th>Date</th><th>Prix</th><th>N</th></tr>'
    for i in d['igs'].keys():
        if len(i) == 10:
            url = d['igs'][b'%'+i]
            src, dat = btob64(d['igs'][i][:9]), datdecode(d['igs'][i][9:13])
            xi, p1, pf = valdecode(d['igs'][i][13:20])
            o += '<tr><td><a class="mono" href="http://%s">%s</a></td><td class="mono">%s</td><td class="num">%s</td><td class="num">%d/%d&nbsp;⊔ (%d%%)</td><td class="num">%s</td></tr>' % (url.decode('utf8'), btob64(i), src, dat, p1, pf, xi, (len(d['igs'][i])-152)//9)
    o += '</table>'

    o += '<table><tr><th>Trans. src</th><th>Date</th><th>Destinataire</th><th>Message</th><th>Montant</th></tr>'
    for t in d['trx'].keys():
        if len(t) == 13 and d['trx'][t][:1] == b'A':
            cry = btob64(d['trx'][t][:1])
            dat, src, dst, val = datdecode(t[:4]), btob64(t[4:13]), btob64(d['trx'][t][1:10]), b2i(d['trx'][t][10:13])
            desc = d['trx'][t][13:-132].decode('utf8')
            value = '%9d&nbsp;⊔' % val if cry == b'U' else '%7.2f&nbsp;€' % (val/100)
            o += '<tr><td class="mono">%s</td><td class="num">%s</td><td class="mono">%s</td><td>%s</td><td class="num">%s</td></tr> ' % (src, dat, dst, desc, value)
    o += '</table>'

    o += '<table><tr><th>Trans. src</th><th>Date</th><th>Destinataire</th><th>Message</th></tr>'
    for t in d['trx'].keys():
        if len(t) == 13 and d['trx'][t][:1] == b'C':
            dat, src, dst = datdecode(t[:4]), btob64(t[4:13]), btob64(d['trx'][t][1:10])
            desc = d['trx'][t][10:-132].decode('utf8')
            o += '<tr><td class="mono">%s</td><td class="num">%s</td><td class="mono">%s</td><td>%s</td></tr> ' % (src, dat, dst, desc)
    o += '</table>'

    o += '<table><tr><th>Trans. src</th><th>Date</th><th>No</th><th>IG</th><th>Destinataire</th><th>Montant</th></tr>'
    for t in d['trx'].keys():
        if len(t) == 14:
            nb, ig, hig, src, dat = b2i(t[:4]), t[4:], btob64(t[4:14]), btob64(d['trx'][t][:9]), datdecode(d['trx'][t][9:13])
            dst = btob64(d['igs'][ig][:9])
            prc = price(d['igs'], ig, nb)
            o += '<tr><td class="mono">%s</td><td class="num">%s</td><td class="num">%05d</td><td class="mono">%s</td><td class="mono">%s</td><td class="num">%d&nbsp;⊔</td></tr> ' % (src, dat, nb, hig, dst, prc)
    o += '</table>'
    o += '<table><tr><th>Errors</th></tr>'
    #su =  sum([blc(d, u) + blc(d, u, b'U') for u in d['pub'].keys()])     
    su =  sum([blc(d, u) for u in d['pub'].keys()])     
    if su != 0: o += '<tr><td class="num">Balances: %s</td></tr> ' % su
    k = ecdsa()
    for t in d['trx'].keys():
        if len(t) == 13:
            src, cry, dst, msg, sig = t[4:], d['trx'][t][:1], d['trx'][t][1:10], t + d['trx'][t][:-132], d['trx'][t][-132:]
            k.pt = Point(c521, b2i(d['pub'][src][:66]), b2i(d['pub'][src][66:]+src))
            if src in d['pub'] and dst in d['pub'] and src != dst:
                if not k.verify(sig, msg): 
                    o += '<tr><td class="mono">%s %s</td></tr>' % (datdecode(t[:4]), btob64(t[4:]))
            else:
                '<tr><td class="mono">Pb!</td></tr>'
    if b'_' in d['crt']: # REFAIRE
        root = d['crt'][b'_']
        if root in d['pub']:
            k.pt = Point(c521, b2i(d['pub'][root][:66]), b2i(d['pub'][root][66:]+root))
            for c in d['crt'].keys():
                if len(c) == 9 and not k.verify(d['crt'][c][12:], c + d['crt'][c][:12]): 
                    o += '<tr><td class="mono">certificat</td></tr>'
    o += '</table>'
    atrt = btob64(d['crt'][b'_'])[:5] if b'_' in d['crt'] else 'None'
    return o + footer('%s %s Auth:%s' % (rdigest(env['SERVER_PORT']), stat(d), atrt)) + '</body></html>\n'

def rates(d, env):
    "_"
    o = '<?xml version="1.0" encoding="utf8"?>\n<html>\n'
    o += '<meta name="viewport" content="width=device-width, initial-scale=1"/>'
    o += favicon() + style_html(False) + '<body><div class="bg"></div>' + header()
    now, db = '%s' % datetime.datetime.now(), '/%s/rates' %__app__
    dr = dbm.open(db) 
    tmp = [(time.mktime(time.strptime(x.decode('ascii'),'%Y-%m-%d')), x, dr[x]) for x in dr.keys()]
    first = True
    y, R, RR = {}, 1, []
    for i, x in enumerate(sorted(tmp)):
        h = eval(x[2].decode('ascii'))
        s1, s2 = 1, 1
        if first:
            h['KUP'], first = .1, False
        else:
            for c in filter(lambda i:i!='USD', __curset__):
                s1 += h[c]/y[c]*__curset__[c]
                s2 += h[c]*h[c]/y[c]/y[c]*__curset__[c]            
            h['KUP'] = y['KUP']*s1/s2
            R *= s1/s2
            RR.append(R)
        y = h
    o += '<p>%s %s</p>' % (now[:19], R)
    o += '<svg %s width="100%%" height="500">\n' % (_SVGNS)
    o += '<rect x="10" y="10" width="95%%" height="300" style="stroke:gray;fill:none"/>\n'
    gain, offset = 4000, 300
    for c in __curset__:
        if c != 'USD':
            l1 = ''
            for i, x in enumerate(sorted(tmp)):
                tot = eval(x[2].decode('ascii'))
                if i == 0: dec = tot[c]*gain
                l1 += 'L%s,%s' % (10*i, int(tot[c]*gain - dec + offset))
            o += '<path d="M%s" style="stroke:%s;stroke-width:1;fill:none;"/>\n' % (l1[1:], 'blue' if c == 'KUP' else 'red')  
    l1 = ''
    for i, r in enumerate(RR):
        if i == 0: dec = r*gain
        l1 += 'L%s,%s' % (10*i, int(r*gain - dec + offset))
        o += '<path d="M%s" style="stroke:blue;stroke-width:1;fill:none;"/>\n' % l1[1:]
    o += '</svg>'
    dr.close()
    atrt = btob64(d['crt'][b'_'])[:5] if b'_' in d['crt'] else 'None'
    return o + footer('%s %s Auth:%s' % (rdigest(env['SERVER_PORT']), stat(d), atrt)) + '</body></html>\n'

def rates_old(d, env):
    "_"
    o = '<?xml version="1.0" encoding="utf8"?>\n<html>\n'
    o += '<meta name="viewport" content="width=device-width, initial-scale=1"/>'
    o += favicon() + style_html() + '<body><div class="bg"></div>' + header()
    now = '%s' % datetime.datetime.now()
    o += '<p>%s<br/> 1 ⊔ = ...</p>' % now[:19]
    res = forex_read()
    for i in res: o += '<p class="num">...%s %s</p>' % (res[i], i)
    atrt = btob64(d['crt'][b'_'])[:5] if b'_' in d['crt'] else 'None'
    return o + footer('%s %s Auth:%s' % (rdigest(env['SERVER_PORT']), stat(d), atrt)) + '</body></html>\n'

def upload(env):
    "_"
    o = '<?xml version="1.0" encoding="utf8"?>\n<html>\n'
    o += '<meta name="viewport" content="width=device-width, initial-scale=1"/>'
    o += favicon() + style_html(False) + header()
    o += '<form enctype="multipart/form-data" method="post"><input type="file"/><input type="submit" value="Go"/></form>'
    o += '<p>%s</p>' % env
    return o + footer() + '</body></html>\n'

def enurl(d, dr, ign, pos):
    "_"
    hig, k = hcode(ign), ecdsa()
    dst = d['igs'][hig][143+pos*9:152+pos*9]
    k.pt = Point(c521, b2i(d['pub'][dst][:66]), b2i(d['pub'][dst][66:]+dst))
    t = i2b(pos-1, 4) + hig
    if t in d['trx']:
        if t in dr: eurl = dr[t]
        else:
            rurl = random_b64()
            eurl = k.encrypt(rurl)
            dr[rurl], dr[t] = ign, eurl
        return eurl
    return None

def publish(d, dr, env, ign, pos):
    "_"
    o = '<?xml version="1.0" encoding="utf8"?>\n<html>\n'
    o += '<meta name="viewport" content="width=device-width, initial-scale=1"/>'
    o += favicon() + style_html(False) 
    di = '/%s/%s_%s/%s' % (__app__, __app__, env['SERVER_PORT'], ign)
    fpdf, fpng, lpng = di + '.pdf', di + '.png', di + '_.png'
    if os.path.isfile(fpdf):
        p = subprocess.Popen(('pdfinfo', fpdf), stdout=subprocess.PIPE).communicate()
        nump = int(reg.v.group(1)) if reg(re.search('Pages:\s+(\d+)', p[0].decode('ascii'))) else 0
        if not os.path.isfile (bytes(fpng, 'utf8')): subprocess.call(('convert', 'x300', (fpdf + '[0]').encode('utf8') , fpng.encode('utf8')))
        if not os.path.isfile (bytes(lpng, 'utf8')): subprocess.call(('convert', 'x300', (fpdf + '[%s]' % (nump-1)).encode('utf8') , lpng.encode('utf8')))
        data = base64.b64encode(open(fpng.encode('utf8'), 'rb').read()).decode('ascii')
        datb = base64.b64encode(open(lpng.encode('utf8'), 'rb').read()).decode('ascii')
        o += '<h1>%s</h1>' % ign
        o += '<h2>%d pages</h2>' % nump
        o += '<a href="/%s.png" title="page de couverture"><img class="book" width="150" src="data:image/png;base64,%s"/></a>\n' % (ign, data)
        o += '<a href="/%s_.png" title="quatrième de couverture"><img class="book" width="150" src="data:image/png;base64,%s"/></a>\n' % (ign, datb)
        hig = hcode('%s/publish/%s' % (env['SERVER_NAME'], ign))
        if hig in d['igs']:
            src, dat, nb = d['igs'][hig][:9], datdecode(d['igs'][hig][9:13]), (len(d['igs'][hig])-152)//9
            xi, p1, pf = valdecode(d['igs'][hig][13:20])
            o += '<p>Code IG: <b class="mono">%s</b></p>' % btob64(hig)
            o += '<p>Auteur: <a class="mono" href="/?%s">%s</a></p>' % (btob64(src), btob64(src))
            o += '<p>Date de publication: %s</p>' % dat
            o += '<p>Prix Initial: %d&nbsp;⊔</p>' % p1
            o += '<p>Revenu cumulé maximum escompté: %d&nbsp;⊔</p>' % pf
            o += '<p>Paramètre de vitesse: %d%%</p>' % xi
            o += "<p>Nombre d'acheteurs: %6d</p>" % nb
            o += "<p><b>Prochain Prix %7.2f&nbsp;⊔</b></p>" % price(d['igs'], hig, 0, True)
            o += "<p><b>Revenu courant %7.2f&nbsp;⊔</b></p>" % income(d['igs'], hig)
            if pos != None and int(pos)<=nb and int(pos)>0:
                ign2 = '%s/publish/%s' % (env['SERVER_NAME'], ign)
                eurl = enurl(d, dr, ign2, int(pos))
                if eurl: o += '<div class="qr" title="%s">%s</div>\n' % (btob64(eurl), QRCode(btob64(eurl), 2).svg(0, 0, 4))
    else:
        o += 'IG not found' 
    atrt = btob64(d['crt'][b'_'])[:5] if b'_' in d['crt'] else 'None'
    return o + '</body></html>\n'

def diff_dbs(d, port):
    "_"
    tab = []
    for p in d['prs'].keys(): 
        if rdigest(port) != digest_req(p.decode('utf8')).decode('utf8'): 
            tab.append(p)
    if tab: hmerge(d, port, tab)

def push_dbs(d, port):
    "_"
    for q in [p for p in filter(lambda i: rdigest(port) != digest_req(i.decode('utf8')).decode('utf8'), d['prs'].keys())]: 
        req(q.decode('utf8'), 'TRX%s' % {x: d['trx'][x] for x in d['trx'].keys()})
        req(q.decode('utf8'), 'CRT%s' % {x: d['crt'][x] for x in d['crt'].keys()})
        req(q.decode('utf8'), 'PUB%s' % {x: d['pub'][x] for x in d['pub'].keys()})
        req(q.decode('utf8'), 'IGS%s' % {x: d['igs'][x] for x in d['igs'].keys()})

def valid_pub(d, pub):
    "_"
    cm, key = pub[-9:], pub[:-9]
    if cm not in d['pub']:
        d['pub'][cm] = key
        return True
    return False

def valid_ig(d, dig, url):
    "_"
    k, h, src, r, msg, sig = ecdsa(), dig[:10], dig[10:19], dig[10:], dig[:30], dig[30:]
    k.pt = Point(c521, b2i(d['pub'][src][:66]), b2i(d['pub'][src][66:]+src))
    if h not in d['igs']:
        if k.verify(sig, msg):
            d['igs'][h] = r
            d['igs'][b'%'+h] = url
            return True
    return False

def valid_big(d, r):
    "validate buying IG"
    "TBD: check that the date is not the same!"
    k, hig, src, dat, msg, sig = ecdsa(), r[:10], r[10:19], r[19:23], r[:23], r[23:]
    if src in d['pub'] and hig in d['igs']:
        k.pt, ssrc = Point(c521, b2i(d['pub'][src][:66]), b2i(d['pub'][src][66:]+src)), b'&'+src
        if price(d['igs'], hig, 0, True) <= blc(d, src, b'U') and k.verify(sig, msg): 
            nb = i2b((len(d['igs'][hig]) - 152)//9, 4)
            d['trx'][nb + hig] = src + dat + sig
            d['igs'][hig] += src
            d['trx'][ssrc] = d['trx'][ssrc] + hig if ssrc in d['trx'] else hig # shortcut
            return True
    return False

def valid_trx(d, r):
    "_"
    u, dat, src, v, cry, dst, prc, msg, sig, k = r[:13], r[:4], r[4:13], r[13:-132], r[13:14], r[14:23], r[23:26], r[:-132], r[-132:], ecdsa()
    k.pt, ddst = Point(c521, b2i(d['pub'][src][:66]), b2i(d['pub'][src][66:]+src)), b'%'+dst
    if src in d['pub'] and dst in d['pub'] and src != dst and u not in d['trx'] and k.verify(sig, msg):
        if cry == b'C':
            d['trx'][u] = v + sig
            return True
        if ((cry == b'U' and (src in d['crt'] or dst in d['crt'])) or cry == b'A') and (blc(d, src, cry) + debt(d, src, cry) > b2i(prc)):
            d['trx'][u] = v + sig
            d['trx'][src] = d['trx'][src] + dat if src in d['trx'] else dat # shortcut
            d['trx'][ddst] = d['trx'][ddst] + u if ddst in d['trx'] else u  # shortcut
            return True
    return False

def valid_crt(d, r):
    "_"
    dst, dat, src, hsh, msg, sig, k = r[:9], r[9:13], r[13:22], r[22:34], r[:-132], r[-132:], ecdsa()
    k.pt, ddst = Point(c521, b2i(d['pub'][src][:66]), b2i(d['pub'][src][66:]+src)), b'%'+dst
    if src in d['crt'] and len(d['crt'][src]) == 136: # check root signature
        if src in d['pub'] and dst in d['pub'] and src != dst and k.verify(sig, msg):
            d['crt'][dst] = dat + src + hsh + sig
            return True
    return False

def find_trx(d, r):
    o, un = '<?xml version="1.0" encoding="utf8"?>\n<html>\n', '<euro>&thinsp;€</euro>'
    o += '<meta name="viewport" content="width=device-width, initial-scale=1"/>'
    u, dat, src, v, cry, dst, prc, msg, sig, m, k = r[:13], r[:4], r[4:13], r[13:-132], r[13:14], r[14:23], r[23:26], r[:-132], r[-132:], r[26:-132].decode('utf8'), ecdsa()
    qrurl = 'http://eurofranc.fr/' + btob64(u)
    o += '<div class="qr" title="%s">%s</div>\n' % (qrurl, QRCode(qrurl, 2).svg(0, 0, 4))
    res = '<b class="huge red" title="Erreur !"">⚠</b>'
    k.pt, ddst = Point(c521, b2i(d['pub'][src][:66]), b2i(d['pub'][src][66:]+src)), b'%'+dst
    if src in d['pub'] and dst in d['pub'] and src != dst and u in d['trx'] and k.verify(sig, msg):
        if blc(d, src, cry) + debt(d, src, cry) > b2i(prc):
            typs, typd = get_type(d, src), get_type(d, dst)
            res = '<br/><b class="huge green" title="Transaction validée">✔</b><p><b>%s</b></p><p><big><big><b>%7.2f%s</b></big></big></p><p>De: <img src="%s"/> <a class="mono" href="/%s">%s</a></p><p>&nbsp;&nbsp;À: <img src="%s"/> <a class="mono" href="/?%s">%s</a></p><p>Message: <b>%s</b></p>' % (datdecode(dat), float(b2i(prc)/100), un, get_image('www/user32.png'), btob64(src), btob64(src), get_image('www/user32.png'), btob64(dst), btob64(dst), m)
    o += favicon() + style_html(False) + '<body><div class="bg"></div>' + header()
    atrt = btob64(d['crt'][b'_'])[:5] if b'_' in d['crt'] else 'None'
    return o + res + footer('Authority: %s' % (atrt) ) + '</body></html>\n'

def application(environ, start_response):
    "wsgi server app"
    mime, o, now, fname, port = 'text/plain; charset=utf8', 'Error:', '%s' % datetime.datetime.now(), 'default.txt', environ['SERVER_PORT']
    d = init_dbs(('prs', 'trx', 'pub', 'crt', 'igs'), port)
    dr = dbm.open('/%s/%s_%s/url' % (__app__, __app__, port), 'c')                
    wdigest(d, port)
    d['crt'][b'_'] = b64tob(bytes(_root_id, 'ascii'))
    (raw, way) = (environ['wsgi.input'].read(), 'post') if environ['REQUEST_METHOD'].lower() == 'post' else (urllib.parse.unquote(environ['QUERY_STRING']), 'get')
    base, ncok = environ['PATH_INFO'][1:], []
    if way == 'post':
        arg = urllib.parse.unquote_plus(raw.decode('utf8'))
        if arg == 'PEERS': o = '%s' % {x.decode('utf8'): d['prs'][x].decode('utf8') for x in d['prs'].keys()}
        elif arg == 'rem=Effacer les cookies':
            for x in environ['HTTP_COOKIE'].split(';'):
                t = x.split('=')
                ncok.append(('set-cookie', '%s=no;expires=Thu, 01 Jan 1970 00:00:00 GMT' % t[0]))            
            del environ['HTTP_COOKIE']
            o, mime = index(d, environ), 'text/html; charset=utf-8'
        elif reg(re.match(r'(TRX|CRT|PUB|IGS)', arg)):
            li, la, db = eval(urllib.parse.unquote(arg[3:])), {}, reg.v.group(1).lower()
            # not used for for pushing! 
            #for x in d[db].keys():
            #    if x not in li: la[x] = d[db][x]
            if li: update_db(db, d, li)
            wdigest(d, port)
            o = '%s' % la
        elif arg == 'DIGEST': o = rdigest(port)
        elif arg == 'IBANK': o = get_random_ibank(d['crt'])
        elif reg(re.match('(cm=(\S{1,12})&)prc=([\d\.\,]{1,7})\s*€?$', arg)):
            prc = int(float(re.sub(',', '.', reg.v.group(3)))*100)
            r = capture_id(d, reg.v.group(2))
            o, mime = index(d, environ, r, prc), 'text/html; charset=utf-8'
        elif reg(re.match('cm=(\S{1,12})&alias=(.+)$', arg)):
            r, ok = capture_id(d, reg.v.group(1)), True
            if r:
                if 'HTTP_COOKIE' in environ:
                    for x in environ['HTTP_COOKIE'].split(';'):
                        t = x.split('=')
                        if reg.v.group(2) == t[0] or r == t[1]: ok = False
                        #if reg.v.group(2) == t[0]: ok = False # revoir pour changement alias!
                if ok:
                    xprs = time.time() + 100 * 24 * 3600 # 100 days from now
                    alia = urllib.parse.quote(reg.v.group(2))
                    ncok.append(('set-cookie', '%s=%s;expires=%s GMT' % (alia, r, time.strftime('%a, %d-%b-%Y %T', time.gmtime(xprs)))))
                    if 'HTTP_COOKIE' in environ:
                        environ['HTTP_COOKIE'] += ';%s=%s' % (alia, r)
                    else:
                        environ['HTTP_COOKIE'] = '%s=%s' % (alia, r)
                o, mime = index(d, environ, r), 'text/html; charset=utf-8'
            else:
                o += 'Id not found! |%s|' % arg 
        elif reg(re.match('([^:]+):(\d+)$', arg)):
            ign2 = '%s/%s' % (environ['SERVER_NAME'], reg.v.group(1))
            eurl = enurl(d, dr, ign2, int(reg.v.group(2)))
            if eurl: o = btob64(eurl)
        elif re.match('\!\S{1,15}$', arg): o = capture_ig(d, arg[1:])
        elif re.match('\?\S{1,12}$', arg): o = capture_id(d, arg[1:])
        elif re.match('\=\S{12}$', arg):
            u = b64tob(bytes(arg[1:], 'ascii'))
            o = '%s:%s:%s' % (blc(d, u)/100, blc(d, u, b'U'), debt(d, u))
        elif re.match('@\S{174,176}$', arg): 
            if valid_pub(d, b64tob(bytes(arg[1:], 'ascii'))): o = 'New public key registered [%s]' % len(d['pub'])
            else: o += 'public key already registered!'
        elif re.match('&\S{216}', arg): 
            if valid_ig(d, b64tob(bytes(arg[1:217], 'ascii')), arg[217:]): o = 'New IG registered [%s]' % len(d['igs'])
            else: o += 'IG already registered!'
        elif re.match('\*\S{207}$', arg): 
            if valid_big(d, b64tob(bytes(arg[1:], 'ascii'))): o = 'New IG(⊔) transaction recorded [%s]' % len(d['trx'])
            else: o += 'not valid ig transaction !'
        elif re.match('\+\S{211,237}$', arg):
            if valid_trx(d, b64tob(bytes(arg[1:], 'ascii'))) : o = 'New transaction recorded [%s]' % len(d['trx'])
            else: o += 'not valid transaction !'
        elif re.match('\.\S{222}$', arg): 
            if valid_crt(d, b64tob(bytes(arg[1:], 'ascii'))) : o = 'New certificat recorded [%s]' % len(d['crt'])
            else: o += 'not valid certification !'
        elif arg[:10] == '-'*10:
            l2 = environ['wsgi.input'].read()
            l2 = environ.get('wsgi.post_form').read()
            o = 'OK upload %s %s %s' % (arg, len(arg), l2)
        else: o += 'not valid args |%s| %s' % (arg, len(arg))
    else: # get
        if base == '2015': o, mime = membership(), 'text/html; charset=utf-8'
        elif re.match('[A-Za-z\d\-_]{12}$', base): o, mime = index(d, environ, base), 'text/html; charset=utf-8'
        elif re.match('\S{18}$', base):
            u = b64tob(bytes(base, 'ascii'))
            o, mime = find_trx(d, u + d['trx'][u]), 'text/html; charset=utf-8'
        elif re.match('\+\S{211,237}$', base): 
            o, mime = find_trx(d, b64tob(bytes(base[1:], 'ascii'))), 'text/html; charset=utf-8'
        elif base == 'peers': # propagation
            fullbase, li = urllib.parse.unquote(environ['REQUEST_URI'])[1:], {}
            for p in d['prs'].keys(): li.update(peers_req(p.decode('utf8')))
            o = update_peers(environ, d['prs'], li)
            #diff_dbs(d, port)
        elif base == '_update': o, mime = app_update(environ['SERVER_NAME']), 'text/html; charset=utf-8'
        elif base == 'dashboard': o, mime = dashboard(d, environ), 'text/html; charset=utf-8'
        elif base == 'rates': o, mime = rates(d, environ), 'text/html; charset=utf-8'
        elif base == 'upload': o, mime = upload(environ), 'text/html; charset=utf-8'
        elif reg(re.match('(\S+)\.png$', base)): 
            mime, o = 'image/png', open('/%s/%s_%s/%s.png' % (__app__, __app__, port, reg.v.group(1)), 'rb').read()
        elif reg(re.match('publish/([^:]+)(|:(\d+))$', base)): o, mime = publish(d, dr, environ, reg.v.group(1), reg.v.group(3)), 'text/html; charset=utf-8'
        elif re.match('\S{20}$', base): 
            url = bytes(base, 'utf8')
            if url in dr: 
                o, mime = open('/%s/%s_%s/%s.pdf' % (__app__, __app__, port, dr[url].decode('utf8')), 'rb').read(), 'application/pdf'
            else:
                o += 'bad url!'
        elif base == '':
            if raw == 'install': o = install()
            elif raw == 'ios': o = 'Toujours en phase de test!\nBientôt disponible sur appStore\n\nNous contacter pour toute question.'
            elif raw == 'src': o = open(__file__, 'r', encoding='utf-8').read() 
            elif raw == 'download': o, mime = open(__file__, 'r', encoding='utf-8').read(), 'application/octet-stream' 
            elif raw == 'bank': o, mime = bank(d, environ), 'text/html; charset=utf-8'
            elif raw == 'ibank': o, mime = ibank(), 'text/html; charset=utf-8'
            elif raw == 'simu': o, mime = simu(d, environ, 10, 1000), 'text/html; charset=utf-8'
            elif reg(re.match('p=(\d+)&f=(\d+)$', raw)): o, mime = simu(d, environ, int(reg.v.group(1)), int(reg.v.group(2)), True), 'text/html; charset=utf-8'
            elif reg(re.match('p=(\d+)&f=(\d+)&i=(\d+)$', raw)): 
                pu, pi, i = int(reg.v.group(1)), int(reg.v.group(2)), int(reg.v.group(3)) 
                p, k = func_price(pu, pi, i)
                t = (i+1-k)*(p+1) +k*p
                o = '%s*%s⊔ + %s*%s⊔ = %s⊔' % (i+1-k, p+1, k, p, t)
            else:
                o, mime = index(d, environ, raw), 'text/html; charset=utf-8'
                #diff_dbs(d, port)
        elif re.match(r'\S{2,40}', base) and base != environ['HTTP_HOST']: # bootstrap
            li = peers_req(base) 
            li.update({base:now[:19]})
            o = update_peers(environ, d['prs'], li)
            #diff_dbs(d, port)
            push_dbs(d, port)
        else:
            o += 'request not valid!'
    for db in d: d[db].close()
    dr.close()
    start_response('200 OK', [('Content-type', mime)] + ncok)
    return [o if mime in ('application/pdf', 'image/png', 'image/jpg') else o.encode('utf8')] 

def wdigest(d, port):
    "computes digest for all databases"
    dbs = ('pub', 'trx', 'crt')
    s = b''.join([b''.join([x + d[a][x] for x in sorted(d[a].keys())]) for a in dbs])
    open('/%s/%s_%s/digest.txt' % (__app__, __app__, port) , 'w').write(hashlib.sha1(s).hexdigest()[:10])

def rdigest(port):
    "return db digest"
    return open('/%s/%s_%s/digest.txt' % (__app__, __app__, port)).read()

def install():
    """Quelques instructions d'installation sous Linux\n
- Sauvegarder le fichier source avec le nom '%s.py'
- Créez un répertoire /%s à la racine avec les droits d'écriture pour www-data
- Installer un serveur Web; le plus simple est Apache2 le mod 'wsgi' pour Python3 
sudo apt-get install apache2 libapache2-mod-wsgi-py3
- Configurer Apache en ajoutant un fichier ppc.conf sous /etc/apache/conf.d avec la ligne:
WSGIScriptAlias / /home/mon_repertoire_installation/%s.py
- Relancer le serveur Apache
sudo /etc/init.d/apache restart
- Ouvrez la page installée:
"http://mon_serveur/"
une copie des bases 'prs'(peers), 'trs' (transactions), 'pub'(public keys), 'igs' (Intangibles GoodS) et 'crt' (certificats) 
est installée dans le répertoire /%s
- enfin lancez '%s.py add' en ligne de commande pour générer vos clés
votre clé privée est dans le fichier 'keys'...à protéger absolument des intrus et à ne pas perdre.\n
Pour tout problème ou question, nous contacter à 'contact@cupfoundation.net'
"""
    return install.__doc__ % (__app__, __app__, __app__, __app__, __app__)

##### MAIN #####

def simulate2():
    p1, pf = 10, 100
    R = [(0,0)]*(pf+20)
    T = p1
    for i in range (pf+20):
        m = 100000
        r = int(p1*(1-i/pf))
        pt = r if r>=0 else 0
        tt = p1+i if i<pf else pf
        for t in range(T, pf+1):
            for k in range (i+2):
                for p in range(p1+1):
                    if (i+1-k)*(p+1) + k*p == t:
                        v = (pt-p)*(pt-p) + (tt-t)*(tt-t)
                        if v <= m and t>=T: 
                            m, T, R[i] = v, t, (p, k)
    for i, x in enumerate(R):
        (p, k) = x
        print (i, '%s*%s+%s*%s=%s' % (i+1-k, p+1, k, p , (i+1-k)*(p+1) + k*p))
    sys.exit()

def simulate():
    "_"
    pu, pi = 10, 100
    print ('%d⊔ %s⊔' % (pu, pi))
    fo, po, ko, mo = False, 0, 0, 0 ## check double price ##   
    for i in range(pi+10): 
        p, k = func_price(pu, pi, i)
        t = (i+1-k)*(p+1) +k*p
        print ('%s*%s⊔ + %s*%s⊔ = %s⊔' % (i+1-k, p+1, k, p, t))
        ## begin - check double price and increase income## 
        if p==po:
            if 1+ko > k:
                if fo and t <= pi: assert False
            else: fo = True
        else: fo = False
        if t >= mo: mo = t
        else: assert False
        assert k>=0 and k<=i+1 and p>=0
        po, ko = p, k   
        ## end check ##
    sys.exit()

def simul_table(verif=True):
    "_"
    pu, pi, ta = 10, 1000, []
    for i in range(pi+2+1): ta.append(['%04s ' % i]) 
    for xi in (0, 15, 30, 40, 60, 70, 85, 100):
        ta[0].append('%016s' % xi)
        fo, po, ko, mo = False, 0, 0, 0 ## check double price ##   
        for i in range(pi+2): 
            p, k = func_price(pu, pi, i)
            t = (i+1-k)*(p+1) +k*p
            dp = '%s*%s+%s*%s=%s' % (i+1-k, p+1, k, p, t)
            #dp = '%s %s' % (p, k)
            ta[i+1].append('%16s' % dp)
            ## begin - check double price and increase income## 
            if verif:
                if p==po:
                    if 1+ko > k:
                        if fo and t <= pi: assert False
                    else: fo = True
                else: fo = False
                if t >= mo: 
                    mo = t
                else: 
                    assert False
                assert k>=0 and k<=i+1 and p>=0
            po, ko = p, k   
            ## end check ##
    for l in ta: print (' '.join(l))
    sys.exit()

def get_proof(limite):
    "_"
    for p1 in range(1, limite):
        print('[%s]' % p1)
        #sys.stdout.write(.)
        #sys.stdout.flush()
        for pi in range(2*p1+1, limite):
            #print('<%s>' % pi)
            fo, po, ko, mo = False, 0, 0, 0 ## check double price ##   
            for i in range(3*pi):
                p, k = func_price(p1, pi, i)
                t = (i+1-k)*(p+1) +k*p
                ## begin - check double price and increase income## 
                if p==po:
                    if 1+ko > k:
                        if fo and t <= pi: assert False
                    else: fo = True
                else: fo = False
                if t >= mo: mo = t
                else: assert False
                assert k>=0 and k<=i+1 and p>=0
                po, ko = p, k   
                ## end check ##
    print ('ok!')
    sys.exit()

def fprice_continious(p1, pf, xi, i):
    "function price"
    if xi == 0:
        p = p1//(i+1)
        if p == 0:
            if i < pf: return 0, 0
            else: return 0, i+1-pf
        else:
            return p, (i+1)*(p+1)-p1
    if xi > 100: xi = 100
    l = ((pf-p1)/(pf-2*p1))**(xi/100)
    ta = pf+(p1-pf)/l**i
    p = int(ta/(i+1))
    k, j = (i+1)*(p+1)-round(ta), i
    while True:
        j += 1
        tb = pf+(p1-pf)/l**j
        q = int(tb/(j+1))
        y = (j+1)*(q+1) - round(tb)
        if p != q: break
        if k >= y+i-j: k = y+i-j
        else: break
        if k < 0: k=0; break
        if j+1-y == pf: break
    return p, k

def fprice(p1, pf, xi, i):
    "function price (pelinquin)"
    j, g = 0, 1 + int(xi/100*(p1-1))
    if i+1 < p1/g:
        p = int(p1/(i+1))
        return p, (i+1)*(p+1)-p1              #phase1
    elif g*(i+1) < pf: 
        return (0, 0) if g == 1 else (g, i+1) #phase2
    else: 
        while True: 
            j += 1
            k = (i+1)*(p1-j+1)-pf
            if k < i+1: return p1-j, k        #phase3 


def func_price(p1, pf, i):
    """ 
    Return p, k 
    Ensure p decreasing/i for all x in [0,i]
    """
    assert p1>0 and pf>=p1 and i>=0
    if p1*(i+1) < pf: return p1-1, 0
    for j in range(p1):
        k = (p1-j)*(i+1)-pf
        if k < i+1: return p1-j-1, k

def func_price(p1, pf, j):
    R, T = [(0,0)]*(j+1), p1
    for i in range (j-1, j+1):
        m, r, q = p1*p1+pf*pf, int(p1*(1-i/pf)), p1+5*i
        pt, tt = r if r>=0 else 0, q if q<pf else pf
        for t in range(T, pf+1):
            for k in range (i+2):
                for p in range(p1+1):
                    if (i+1-k)*(p+1) + k*p == t:
                        v = (pt-p)*(pt-p) + (tt-t)*(tt-t)
                        if v <= m and t >= T: 
                            m, T, R[i] = v, t, (p, k)
    return R[j]

def func_price1(p1, pf, i):
    "_"
    r = int(p1*(1-i/pf))
    z = i if i<pf else pf
    g = r if r>=0 else 0
    for j in range(p1):
        k = (p1-j)*(i+1)-pf
        if   k < 0: p, k = p1-1, 0; print ((g-p)*(g-p)); return p, k
        elif k < i+1: p = p1-1-j; print ((g-p)*(g-p)); return p, k
    return p, k

def func_verif(p1, pf, i, l):
    "Ensure return value p decreasing/i for all l, p1, pf "
    assert p1>0 and pf>=p1 and i>=0 and l<=i and l>=0
    if p1*(i+1)-pf < 0: return p1 if l <= i-k else p1-1
    for j in range(p1):
        k = (p1-j)*(i+1)-pf
        if k < i+1: return p1-j if l <= i-k else p1-j-1

def func_income(p1, pf, i):
    "_"
    assert p1>0 and pf>=p1 and i>=0
    if p1*(i+1)-pf < 0: return (i+1)*p1
    for j in range(p1): 
        if k < i+1: return pf

def price(digs, ig, l, nxt=False):
    "_"
    xi, p1, pf = valdecode(digs[ig][13:20])
    i = (len(digs[ig]) - 152)//9 if nxt else (len(digs[ig]) - 152)//9 - 1
    if nxt: l = i
    p, k = func_price(p1, pf, i)
    return p+1 if l <= i-k else p

def income(digs, ig):
    "_"
    xi, p1, pf = valdecode(digs[ig][13:20])
    if (len(digs[ig]) - 152)//9 == 0: return 0
    i = (len(digs[ig]) - 152)//9 - 1
    return func_income(p1, pf, i)

def get_random_ibank(dc):
    for x in dc.keys():
        if len(x) == 9: return btob64(x)

__curset__ = {'USD':870, 'EUR':334, 'JPY':230, 'GBP':118, 'AUD':86, 
              'CHF':52,  'CAD':46,  'MXN':25,  'CNY':22,  'NZD':20,
              'SEK':18,  'RUB':16,  'HKD':14,  'SGD':14,  'TRY':13}

def forex():
    " "
    now, ytd, db, y, h = '%s' % datetime.datetime.now(), '%s' % (datetime.datetime.now() - datetime.timedelta(days=1)), '/%s/rates' %__app__, {}, {}
    dr, s1, s2 = dbm.open(db, 'c'), __curset__['USD'], __curset__['USD']
    cu, co = datetime.datetime(2014, 1, 1), http.client.HTTPConnection('currencies.apps.grandtrunk.net')
    while cu < datetime.datetime.now():
        cc = '%s' % cu
        if bytes(cc[:10], 'ascii') not in dr:
            for c in __curset__:
                if c != 'USD':
                    print ('grandtrunk request for %s %s' % (c, cc[:10]))
                    co.request('GET', '/getrate/%s/%s/USD' % (cc[:10], c))
                    h[c] = float(co.getresponse().read())
            dr[cc[:10]] = '%s' % h
        cu += datetime.timedelta(days=1)
    dr.close()

def forex_graph():
    " "
    now, db = '%s' % datetime.datetime.now(), '/%s/rates' %__app__
    #__curset__['USD']
    dr = dbm.open(db)
    dr.close()
    return "hello"

def forex_read():
    " "
    now, ytd, db, y, h, res = '%s' % datetime.datetime.now(), '%s' % (datetime.datetime.now() - datetime.timedelta(days=1)), '/%s/rates' %__app__, {}, {}, {}
    dr, s1, s2 = dbm.open(db), __curset__['USD'], __curset__['USD']
    cu, co = datetime.datetime(2014, 1, 1), http.client.HTTPConnection('currencies.apps.grandtrunk.net')
    while cu < datetime.datetime.now():
        cc = '%s' % cu
        cu += datetime.timedelta(days=1)
    cu, first = datetime.datetime(2014, 1, 1), True
    R = 1
    while cu < datetime.datetime.now():
        cc, s1, s2 = '%s' % cu, 1, 1
        h = eval(dr[cc[:10]])
        if first:
            toto = h['EUR']
            h['KUP'], first = .1, False
        else:
            for c in __curset__:
                if c != 'USD':
                    s1 += h[c]/y[c]*__curset__[c]
                    s2 += h[c]*h[c]/y[c]/y[c]*__curset__[c]            
            h['KUP'] = y['KUP']*s1/s2
            R *= s1/s2
        y = h
        cu += datetime.timedelta(days=1)
    fnow = ('%s' % now)[:10] 
    t = eval(dr[fnow])
    for c in __curset__:
        if c == 'USD': 
            res['USD'] = round(toto/10/R, 10)
        else:
            res[c] = round(toto/t[c]/10/R, 10)
    dr.close()
    return res

def usage():
    """node.py [options]
- no argument
list current valid ids, * sign after the currently selected one
- 1 argument:
'usage' or 'help': this page
'add': add a new id (not registered)
'reg': register unregistered ids
<dbfile>: read the content of the db file
<ig_id>: buy this intangible good
- 2 arguments:
'host' <host_name>: select current host
'user' <user_id_substring>: select current id. The substring shall be unique.
'currency' <new_currency>: select local currency (default is €)
<seller_id> <amount>: send to the seller such amount (default is € currency) 
- 3 arguments:
'<pi> <pf> <xi>': create an IG with speed parameter xi, initial price pi and expected income pf
\n\n
PROTOCOL: POST\n
1/REGISTER PUBLIC KEY
  @<pubkey[132]>
2/REGISTER IG
  &<hurl[10]><src[9]><date[4]><val(xi,pi,pf,rs)[8]><signature[132]>
3/BUY €/£/$/U
  +<currency><date[4]><src[9]><dst[9]><price[3]><log[0,20]><signature[132]>
4/BUY IG
  *<nb[4]><refig[10]><src[9]><date[4]><signature[132]>
5/GET id
  !<string>
  return id[9]
6/GET ig 
  ?<string>
  return ig[10]
7/Get BALANCE
  =<src>
  return <bal€>:<bal⊔>:<debt>
  debt is always nul for regular user (not i-bank)
"""
    print (usage.__doc__)

def gui_mairie():
    def call_create():
        vpw1, vpw2 = wpw1.text(), wpw2.text()
        if vpw1 == vpw2: 
            add_local_id2(vpw1) 
            set('host', 'cup')
            msg.showMessage('Merci de relancer ce programme, cette foi avec Internet connecté !')
            sys.exit()
        else:
            msg.showMessage('Vos mots de passe sont différents !')
    def call_validate():
        msg.showMessage('Erreur!')
        msg.show()
    def call_request():
        register('cup')
        if len(wcom.text()) == 5:
            message2('cup', cm, _root_id, wcom.text() + ' ' + wnam.text(), wpw1.text())
            msg.showMessage('Votre demande a été envoyée. Consultez http://eurofranc/%s' %cm)
            sys.exit()
        else:
            msg.showMessage('Erreur sur le code postal \'%s\' !' % wcom.text())
    app = PyQt4.QtGui.QApplication(sys.argv)
    w = PyQt4.QtGui.QWidget()
    vb = PyQt4.QtGui.QVBoxLayout()
    msg = PyQt4.QtGui.QErrorMessage(w)
    #msg = PyQt4.QtGui.QMessageBox(w)
    
    if False:
        toto = random_b64().decode('ascii')[:8]
        lpsw = PyQt4.QtGui.QLabel('Validation de compte principal\nMessage à faire signer sur place:', w)
        f = PyQt4.QtGui.QFont('courier', 30)
        lale = PyQt4.QtGui.QLabel(toto, w)
        lale.setFont(f)   
        lide = PyQt4.QtGui.QLabel('Identifiant', w)
        wide = PyQt4.QtGui.QLineEdit(w)
        lana = PyQt4.QtGui.QLabel('Année de naissance', w)
        wana = PyQt4.QtGui.QLineEdit('0000', w)
        wana.setMaximumWidth(50)
        lscu = PyQt4.QtGui.QLabel('N° Sécurité Sociale', w)
        wscu = PyQt4.QtGui.QLineEdit('', w)
        lpw1 = PyQt4.QtGui.QLabel('Votre Mot de passe', w)
        wpw1 = PyQt4.QtGui.QLineEdit(w)
        wpw1.setEchoMode(PyQt4.QtGui.QLineEdit.Password)
        wval = PyQt4.QtGui.QPushButton('Validez', w)
        wval.clicked.connect(call_validate)

        h0 = PyQt4.QtGui.QHBoxLayout()
        h0.addWidget(lpsw)
        vb.addLayout(h0)

        h0 = PyQt4.QtGui.QHBoxLayout()
        h0.addWidget(lale)
        vb.addLayout(h0)
        
        h1 = PyQt4.QtGui.QHBoxLayout()
        h1.addWidget(lide)
        h1.addWidget(wide)
        vb.addLayout(h1)

        h11 = PyQt4.QtGui.QHBoxLayout()
        h11.addWidget(lana)
        h11.addWidget(wana)
        vb.addLayout(h11)

        h2 = PyQt4.QtGui.QHBoxLayout()
        h2.addWidget(lscu)
        h2.addWidget(wscu)
        vb.addLayout(h2)
        vb.addStretch(1)

        h3 = PyQt4.QtGui.QHBoxLayout()
        h3.addWidget(lpw1)
        h3.addWidget(wpw1)
        vb.addLayout(h3)

        h4 = PyQt4.QtGui.QHBoxLayout()
        h4.addWidget(wval)
        vb.addLayout(h4)

    elif os.path.isfile('keys'):
        db = dbm.open('keys', 'c')
        nb = len(db.keys())
        cm = 'none'
        for x in db.keys():
            if len(x) == 9:
                cm = btob64(x)
                db['user'] = cm
        db.close()
        lpsw = PyQt4.QtGui.QLabel('Vérifiez que cet ordinateur est bien connecté à Internet\nDemande de certification\nde votre identifiant:', w)

        f = PyQt4.QtGui.QFont('courier', 20)
        lacm = PyQt4.QtGui.QLabel(cm, w)
        lacm.setFont(f)   

        wnam = PyQt4.QtGui.QLineEdit('Le nom de votre commune', w)
        wcom = PyQt4.QtGui.QLineEdit('CodePostal', w)
        wcom.setMaximumWidth(86)

        lpw1 = PyQt4.QtGui.QLabel('Votre Mot de passe', w)
        wpw1 = PyQt4.QtGui.QLineEdit(w)
        wpw1.setEchoMode(PyQt4.QtGui.QLineEdit.Password)

        wcrt = PyQt4.QtGui.QPushButton('Envoyez la demande', w)
        wcrt.clicked.connect(call_request)

        h0 = PyQt4.QtGui.QHBoxLayout()
        h0.addWidget(lpsw)
        vb.addLayout(h0)

        h01 = PyQt4.QtGui.QHBoxLayout()
        h01.addWidget(lacm)
        vb.addLayout(h01)

        h1 = PyQt4.QtGui.QHBoxLayout()
        h1.addWidget(wnam)
        h1.addWidget(wcom)
        vb.addLayout(h1)
        vb.addStretch(1)

        h3 = PyQt4.QtGui.QHBoxLayout()
        h3.addWidget(lpw1)
        h3.addWidget(wpw1)
        vb.addLayout(h3)

        h4 = PyQt4.QtGui.QHBoxLayout()
        h4.addWidget(wcrt)
        vb.addLayout(h4)

    else:
        lpsw = PyQt4.QtGui.QLabel('Création de votre Identifiant Mairie\nutilisez un ordinateur dédié\nde préférence déconnecté d\'Internet\nvos clés seront dans le fichier \'keys\'\nne diffusez pas ce fichier', w)
        lpw1 = PyQt4.QtGui.QLabel('Choisisez un mot de passe:', w)
        wpw1 = PyQt4.QtGui.QLineEdit(w)
        wpw1.setEchoMode(PyQt4.QtGui.QLineEdit.Password)
        lpw2 = PyQt4.QtGui.QLabel('Confirmez ce mot de passe:', w)
        wpw2 = PyQt4.QtGui.QLineEdit(w)
        wpw2.setEchoMode(PyQt4.QtGui.QLineEdit.Password)
        wbpw = PyQt4.QtGui.QPushButton('Générer les clés', w)
        wbpw.clicked.connect(call_create)

        h0 = PyQt4.QtGui.QHBoxLayout()
        h0.addWidget(lpsw)
        vb.addLayout(h0)
        vb.addStretch(1)

        h1 = PyQt4.QtGui.QHBoxLayout()
        h1.addWidget(lpw1)
        h1.addWidget(wpw1)
        vb.addLayout(h1)

        h2 = PyQt4.QtGui.QHBoxLayout()
        h2.addWidget(lpw2)
        h2.addWidget(wpw2)
        vb.addLayout(h2)

        h3 = PyQt4.QtGui.QHBoxLayout()
        h3.addWidget(wbpw)
        vb.addLayout(h3)

    w.setLayout(vb)
    w.setWindowTitle('Eurofranc')
    w.setGeometry(50, 50, 320, 480)
    w.show()
    app.exec_()
    

def gui():
    "Qt4"
    def call_buy():
        vcmb = wcmb.currentText()
        vprc = wprc.text()
        vdst = wdst.text()
        vpas = wpas.text()
        vdev = wdev.currentText()
        vigi = wigi.text()
        vmes = wmes.text()
        node = get_host()
        vip1, vipi, vixi, vurl = wip1.text(), wipi.text(), 0, wurl.text()
        if re.match('\d+$', vip1): postig2(node, vcmb, int(vip1), int(vipi), int(vixi), vurl, vpas) 
        elif vigi: buyig2(node, vcmb, vigi, vpas)
        else: buy2(node, vcmb, vdst, vprc, vdev, vpas, vmes)
    def call_create():
        vpas, vpw2 = wpas.text(), wpw2.text()
        if vpas == vpw2: add_local_id2(vpas) 
    def call_postig():
        vpas, vpw2 = wpas.text(), wpw2.text()
        if vpas == vpw2: add_local_id2(vpas) 
    def call_register():
        node = get_host()
        register(node)
    app = PyQt4.QtGui.QApplication(sys.argv)
    w = PyQt4.QtGui.QWidget()
    lcmb = PyQt4.QtGui.QLabel('Source ID', w)
    wcmb = PyQt4.QtGui.QComboBox(w)
    nb = 0
    if os.path.isfile('keys'):
        db = dbm.open('keys', 'c')
        nb = len(db.keys())-2        
        wcmb.addItems([btob64(x) for x in db.keys() if len(x) == 9])
        db.close()
    wcmb.setFocus()
    lhst = PyQt4.QtGui.QLabel('Host', w)
    whst = PyQt4.QtGui.QLineEdit(get_host(), w)
    lidn = PyQt4.QtGui.QLabel('%s IDs locales' % nb, w)
    ldst = PyQt4.QtGui.QLabel('Destinataire ID', w)
    wdst = PyQt4.QtGui.QLineEdit(w)
    lprc = PyQt4.QtGui.QLabel('Prix', w)
    wprc = PyQt4.QtGui.QLineEdit(w)
    wprc.setMaximumWidth(100)
    #wprc.setAlignment(PyQt4.QtCore.Qt.Alignment.right)
    #wprc.setInputMask('0.00')
    wbut = PyQt4.QtGui.QPushButton('Envoyer', w)
    wbut.clicked.connect(call_buy)
    lpas = PyQt4.QtGui.QLabel('Mot de passe', w)
    wpas = PyQt4.QtGui.QLineEdit(w)
    wpas.setEchoMode(PyQt4.QtGui.QLineEdit.Password)
    lmes = PyQt4.QtGui.QLabel('Message', w)
    wmes = PyQt4.QtGui.QLineEdit(w)
    ligi = PyQt4.QtGui.QLabel('Référence IG', w)
    wigi = PyQt4.QtGui.QLineEdit(w)
    wdev = PyQt4.QtGui.QComboBox(w)
    wbt2 = PyQt4.QtGui.QPushButton('Créer un compte', w)
    wbt2.clicked.connect(call_create)
    lpw2 = PyQt4.QtGui.QLabel('Confirmer', w)
    wpw2 = PyQt4.QtGui.QLineEdit(w)
    wpw2.setEchoMode(PyQt4.QtGui.QLineEdit.Password)
    wdev.addItems(['€', '⊔', 'C'])
    wprc.setText('0.00' if wdev.currentText() == '€' else '0') 
    wbt3 = PyQt4.QtGui.QPushButton('Enregistrer les comptes locaux', w)
    wbt3.clicked.connect(call_register)
    ligc = PyQt4.QtGui.QLabel('Nouvel IG', w)
    lip1 = PyQt4.QtGui.QLabel('Prix init.', w)
    wip1 = PyQt4.QtGui.QLineEdit(w)
    lipi = PyQt4.QtGui.QLabel('Revenu max.', w)
    wipi = PyQt4.QtGui.QLineEdit(w)
    #wixi = PyQt4.QtGui.QLineEdit('vitesse %', w)
    wurl = PyQt4.QtGui.QLineEdit('http://', w)
    #
    gb = PyQt4.QtGui.QGroupBox('hello')
    gb.setFlat(True)
    vb = PyQt4.QtGui.QVBoxLayout()
    h0 = PyQt4.QtGui.QHBoxLayout()
    h0.addWidget(lhst)
    h0.addWidget(whst)
    h0.addWidget(lidn)
    vb.addLayout(h0)
    h1 = PyQt4.QtGui.QHBoxLayout()
    h1.addWidget(lcmb)
    h1.addWidget(wcmb)
    vb.addLayout(h1)
    h2 = PyQt4.QtGui.QHBoxLayout()
    h2.addWidget(ldst)    
    h2.addWidget(wdst)
    vb.addLayout(h2)
    h3 = PyQt4.QtGui.QHBoxLayout()
    h3.addWidget(lprc)    
    h3.addWidget(wprc)
    h3.addWidget(wdev)
    vb.addLayout(h3)
    h4 = PyQt4.QtGui.QHBoxLayout()
    h4.addWidget(lmes)    
    h4.addWidget(wmes)
    vb.addLayout(h4)
    h5 = PyQt4.QtGui.QHBoxLayout()
    h5.addWidget(ligi)    
    h5.addWidget(wigi)
    vb.addLayout(h5)
    vb.addStretch(1)

    h6 = PyQt4.QtGui.QHBoxLayout()
    h6.addWidget(ligc)    
    h6.addWidget(wurl)
    vb.addLayout(h6)
    h7 = PyQt4.QtGui.QHBoxLayout()
    h7.addWidget(lip1)
    h7.addWidget(wip1)
    h7.addWidget(lipi)
    h7.addWidget(wipi)
    #h7.addWidget(wixi)
    vb.addLayout(h7)
    h8 = PyQt4.QtGui.QHBoxLayout()
    h8.addWidget(lpas)    
    h8.addWidget(wpas)
    h8.addWidget(wbut)
    vb.addLayout(h8)
    h9 = PyQt4.QtGui.QHBoxLayout()    
    h9.addWidget(lpw2)
    h9.addWidget(wpw2)
    h9.addWidget(wbt2)
    vb.addLayout(h9)
    h10 = PyQt4.QtGui.QHBoxLayout()    
    h10.addWidget(wbt3)
    vb.addLayout(h10)
    #gb.setLayout(vb)
    w.setLayout(vb)
    w.setWindowTitle('Eurofranc')
    w.setGeometry(50, 50, 320, 480)
    w.show()
    app.exec_()

def randrange(order):
    "_"
    byts = (1+len('%x' % order))//2
    #print (b2i(os.urandom(10)))
    cand = b2i(os.urandom(byts))
    return cand//2 if cand >= order else cand


def list_mairies():
    "_"
    host = 'lannuaire.service-public.fr'
    host2 = 'www.annuaire-des-mairies.com'
    deps = ( 
        #'ain', 'aisne', 'allier', 'hautes-alpes', 'alpes-de-haute-provence', 'alpes-maritimes', 'ardeche', 'ardennes', 'ariege', 'aube', 'aude', 'aveyron', 'bouches-du-rhone', 'calvados', 'cantal', 'charente', 'charente-maritime', 'cher', 'correze', 'corse-du-sud', 'haute-corse', 'cote-dor', 'cotes-darmor', 'creuse', 'dordogne', 'doubs', 'drome', 'eure', 'eure-et-loir', 'finistere', 'gard', 'haute-garonne', 'gers', 'gironde', 'herault', 'ile-et-vilaine', 'indre', 'indre-et-loire', 'isere', 'jura', 'landes', 'loir-et-cher', 'loire', 'haute-loire', 'loire-atlantique', 'loiret', 'lot', 'lot-et-garonne', 'lozere', 'maine-et-loire', 'manche', 'marne', 'haute-marne', 'mayenne', 'meurthe-et-moselle', 'meuse', 'morbihan', 'moselle', 'nievre', 'nord', 'oise', 'orne', 'pas-de-calais', 'puy-de-dome', 'pyrenees-atlantiques', 'hautes-pyrenees', 'pyrenees-orientales', 'bas-rhin', 'haut-rhin', 'rhone', 'haute-saone', 'saone-et-loire', 'sarthe', 'savoie', 'haute-savoie', 'paris', 'seine-maritime', 'seine-et-marne', 'yvelines', 'deux-sevres', 'somme', 'tarn', 'tarn-et-garonne', 'var', 'vaucluse', 'vendee', 'vienne', 'haute-vienne', 'vosges', 'yonne', 'territoire-de-belfort', 'essonne', 'hauts-de-seine', 'seine-saint-denis', 'val-de-marne', 'val-doise', 
'mayotte', 'guadeloupe', 'guyane', 'martinique', 'reunion'
)
    serv = '/navigation/'
    co = http.client.HTTPConnection(host)
    d = dbm.open('communes', 'c')
    for x in deps:
        print (x)
        co.request('GET', serv + x + '-mairie.html')
        raw = co.getresponse().read().decode('utf8')
        for m in re.finditer( r'<li><a href="(../mairies/.+)">(.+)</a></li>', raw ):
            co.request('GET', serv + m.group(1) )
            raw2 = co.getresponse().read().decode('latin1')
            if reg(re.search(r'<p class="valeur"><span class="value">(.+)Â \[ Ã  \]Â (.+)</span></p>', raw2)):
                commune, email = m.group(2), '%s@%s' % (reg.v.group(1), reg.v.group(2))
                toto = normalize (commune, x)
                co2 = http.client.HTTPConnection(host2)
                print ('%s -> %s' % (commune, email))                
                co2.request('GET', toto + '.html')
                raw3 = co2.getresponse().read().decode('latin1')
                if reg(re.search(r'Le maire de (.+) se nomme (Monsieur|Madame)(.+)\.', raw3)):
                    typ, name = reg.v.group(2), reg.v.group(3)
                else:
                    typ, name =  'ERREUR', toto
                    print ('%s -> %s:%s:%s' % (commune, email, typ, name))
                d[commune] = '%s:%s:%s' % (email, typ, name)
    d.close()

def normalize(s, x):
    import unicodedata
    s = s.replace('œ', 'oe')
    if reg(re.match(r'(.+) - (\d{4,5})', s)):
        cp = reg.v.group(2) if len(reg.v.group(2)) == 5 else '0' + reg.v.group(2)
        code = cp[:2]
        if x == 'corse-du-sud': 
            code = '2A'
        elif x == 'haute-corse':
            code = '2B'
        elif x == 'guadeloupe':
            code = '971'
        elif x == 'guyane':
            code = '973'
        elif x == 'martinique':
            code = '972'
        elif x == 'reunion':
            code = '974'
        elif x == 'mayotte':
            code = '976'
        return '/%s/' % code + ''.join(c for c in unicodedata.normalize('NFD', reg.v.group(1)) if unicodedata.category(c) != 'Mn').lower().replace(' ','-').replace("'",'-')

if __name__ == '__main__':
    #print (b64toi(_R))
    #print (randrange(b64toi(_R)))
    #k = ecdsa()
    #k.generate()
    #print (k.pt.x, k.pt.y, k.privkey)
    #simulate2()
    #simul_table()
    #simulate()
    #get_proof(50)
    #list_mairies()
    #sys.exit()

    node = get_host() if os.path.isfile('keys') else 'cup'
    if len(sys.argv) == 1:
        forex()
        gui_mairie()
    elif len(sys.argv) == 2:
        if sys.argv[1] in ('list', 'l'): list_local_ids(node)
        elif sys.argv[1] in ('usage', 'help'): usage()
        elif sys.argv[1] == 'add': add_local_id()
        elif sys.argv[1] == 'reg': register(node)
        elif os.path.isfile(sys.argv[1]): readdb(sys.argv[1])
        else: certif(node, sys.argv[1]) #buyig(node, sys.argv[1]) 
    elif len(sys.argv) == 3:
        if sys.argv[1] in ('host', 'user', 'cry'): set(sys.argv[1], sys.argv[2])
        elif re.match('[\d\.\,]+', sys.argv[2]): buy(node, sys.argv[1], float(sys.argv[2]))
        elif os.path.isfile(sys.argv[1]): readdb(sys.argv[1], True)
        else: message(node, sys.argv[1], sys.argv[2])
    elif len(sys.argv) == 4:
        postig(node, int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
    sys.exit()    

# End ⊔net!
