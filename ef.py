#!/usr/bin/python3
# -*- coding: utf-8 -*-
# Welcome to ⊔net!
#-----------------------------------------------------------------------------
#  © Copyright 2015 ⊔Foundation
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
#    * ECDSA has been adapted to Python3 and simplified for NIST521P curve only 
#      code inspired from:
#      Brian Warner  
#    * QRcode is extented to PDF and SVG from the inspired code of:
#      Sam Curren (porting from Javascript)
#-----------------------------------------------------------------------------

# SHORT TODO LIST
# IG registration (local or with the browser)
# Price average (min/max with constraints)
# Add server owner concept to match IGs
# Use of iOS App to buy IGs

# 0 STATE INIT (other color)
# 1 STATE PING (pink color)
#   YES balance + date_now + 
#   NO reference
#   QRCODE srcid+efvalue
#   EDITABLE passwd destid, efvalue
# 2 STATE PONG (blue color)
#   YES reference paybutton
#   NO index/total
#   QRCODE msg+sig
#   EDITABLE: reference 
# 3 STATE CASH (green color) 
#   YES index/total + balance + date_of_transaction + destpicture + array(up or down)
#   NO reference paybutton passwd
#   QRCODE dat+src+val
#   EDITABLE efvalue, dest

# NON REGRESSION TEST COVERAGE 
# 1 enter efvalue
# 2 enter dstid
# 3 enter reference
# 4 enter pwd
# 5 slide right: increment pos
# 6 slide left:  decrement pos
# 7 slide up: last pos
# 8 slide down: init
# 9 double tap: init
# 0 push scan (id:val, msg+sig, transaction_proof)

import re, os, sys, urllib.parse, hashlib, http.client, base64, datetime, functools, subprocess, time, smtplib, operator, getpass, dbm.ndbm, zlib
import requests, requests_oauthlib # for Twitter image capture
import gmpy2 # for inverse_mod fast computing

__app__    = os.path.basename(__file__)[:-3]
__dfprt__  = 80
__base__   = '/%s/%s_%s/' % (__app__, __app__, __dfprt__)
__ef__     = 'eurofranc'
__email__  = 'contact@%s.fr' % __ef__

_b58char   = '123456789abcdefghijkmnopqrstuvwxyzABCDEFGHJKLMNPQRSTUVWXYZ'
_admin_id   = 'AdminJqjFdcY'
_ibank_id   = 'IbankVBixRIm' 
_ibank_id   = 'AdminJqjFdcY'
_admin_pkey = 'AdMctT3bXbwrTBGkB5eKAG74qIqShRRy1nHa_NWCHsxmKhmZeE_aWgo_S251td8d6C5uti6TymQSSZvhmO1b19pIAYYPFxkKL_13dnhBGXdFdmDQhQEZZbc1P7GDDrZZwU0FSGuwc53_AxHk1vVRte7bdmhzIcOUMUvO'
_ibank_pkey = 'AQTMiBfFFaDdokV0d7dPEeyURA_yUmMaXVaQm86YxciRuOpz5oSXdAh2r-6jxdj3cazLExL4B75-V3_hqtbuG_yIAeqq8dmyMTAZUZFBS0fCPK52TzZ6bEyo3H3QHzbk5geIepws4bi2se19WoyZ6xiWDk0COUXLvQAE'   
_ibank_pkey = 'AdMctT3bXbwrTBGkB5eKAG74qIqShRRy1nHa_NWCHsxmKhmZeE_aWgo_S251td8d6C5uti6TymQSSZvhmO1b19pIAYYPFxkKL_13dnhBGXdFdmDQhQEZZbc1P7GDDrZZwU0FSGuwc53_AxHk1vVRte7bdmhzIcOUMUvO'

__curset__ = {'USD':870, 'EUR':334, 'JPY':230, 'GBP':118, 'AUD':86, 'CHF':52,  'CAD':46,  'MXN':25,  'CNY':22,  'NZD':20, 'SEK':18,  'RUB':16,  'HKD':14,  'SGD':14,  'TRY':13}

##### PDF GENERATOR #####

__fonts__ = ('Helvetica', 'Times-Roman', 'Courier', 'Times-Bold', 'Helvetica-Bold', 'Courier-Bold', 'Times-Italic', 'Helvetica-Oblique', 
             'Courier-Oblique', 'Times-BoldItalic', 'Helvetica-BoldOblique', 'Courier-BoldOblique', 'Symbol')
__e__ = '/Euro /ccedilla /' + ' /'.join(['%s%s' % (x,y) for x in ('a','e','i','o','u','y') for y in ('acute', 'grave', 'circumflex', 'dieresis')])

class pdf:
    def __init__(self, pagew, pageh, letterw=595, letterh=842):
        "_"
        self.pw, self.ph = pagew, pageh
        self.mx, self.my = 0, 0
        self.pos = []
        self.o = b'%PDF-1.5\n%\xBF\xF7\xA2\xFE\n'
    
    def add(self, line):
        "_"
        self.pos.append(len(self.o))
        self.o += bytes('%d 0 obj<<%s>>endobj\n' % (len(self.pos), line), 'ascii')

    def addimg(self, img, jpg=False):
        "_"
        self.pos.append(len(self.o))
        tf = open(img, 'rb').read()
        if jpg:
            fil = '/Filter/DCTDecode'
            self.o += bytes('%s 0 obj<</Type/XObject/Subtype/Image/ColorSpace/DeviceRGB/Width 875/Height 1200/BitsPerComponent 8/Length %s%s>>stream\n' % (len(self.pos), len(tf), fil), 'ascii')
        else:
            tf = zlib.compress(tf) 
            fil = '/Filter/FlateDecode'
            self.o += bytes('%s 0 obj<</Type/XObject/Subtype/Form/BBox[0 0 500 500]/FormType 1/Length %s%s>>stream\n' % (len(self.pos), len(tf), fil), 'ascii')
        self.o += tf + bytes('endstream endobj\n', 'ascii')

    def addstream(self, stream):
        "_"
        self.pos.append(len(self.o))
        stream = zlib.compress(stream) 
        fil = '/Filter/FlateDecode'
        self.o += bytes('%d 0 obj<</Length %d%s>>stream\n' % (len(self.pos), len(stream), fil), 'ascii')
        self.o += stream
        self.o += b'endstream endobj\n'

    def addref(self):
        "_"
        self.pos.append(len(self.o))
        n, size = len(self.pos), len(self.o)
        PADA = lambda s:(len(s)%2)*'0'+s
        r = functools.reduce(lambda y, i: y+bytes('01%06x00' % i, 'ascii'), self.pos, b'00000000ff')
        z = zlib.compress(bytes.fromhex(PADA(r.decode('ascii'))))
        self.o += bytes('%s 0 obj<</Type/XRef/Index[0 %s]/Size %s/W[1 3 1]/Root 1 0 R/Length %s/Filter/FlateDecode>>stream\n' % (n, n, n, len(z)), 'ascii') + z + b'endstream endobj\n'
        return size

    def ltext(self, tab, r):
        "_"
        o = b'BT '
        for (x, y, ft, sz, s) in tab: 
            o += bytes('1 0 0 1 %d %d Tm /F%d %d Tf %s TL ' % (x+self.mx+r[0], r[1]-self.my-y, ft, sz, 1.2*sz), 'ascii')
            for l in s.split('\n'): o += bytes('(%s) Tj T* ' % (l), 'ascii')
            o = o[:-3]
        return o + b' ET '

    def ctext(self, tab, r):
        "_"
        o = b'BT '
        for (x, y, ft, sz, c, s) in tab: 
            if c == 1: # vertical left
                o += bytes('.8 .8 .8 rg 0 -1 1 0 %d %d Tm /F%d %d Tf (%s) Tj ' % (x+self.mx+r[0], r[1]-self.my-y, ft, sz, s), 'ascii')
            elif c == 2: # vertical right
                o += bytes('.5 .5 .5 rg 0 1 -1 0 %d %d Tm /F%d %d Tf (%s) Tj ' % (x+self.mx+r[0], r[1]-self.my-y, ft, sz, s), 'ascii')
            elif c == 3: # vertical right light color
                o += bytes('.9 .9 .9 rg 0 1 -1 0 %d %d Tm /F%d %d Tf (%s) Tj ' % (x+self.mx+r[0], r[1]-self.my-y, ft, sz, s), 'ascii')
            else:
                o += bytes('%s rg 1 0 0 1 %d %d Tm /F%d %d Tf (%s) Tj ' % (c, x+self.mx+r[0], r[1]-self.my-y, ft, sz, s), 'ascii')
        return o + b' 0 0 0 rg ET '

    def gen(self, pages):
        "_"
        ft = (1, 3, 5, 8) # font references
        self.add('/Type/Catalog/Pages 2 0 R')
        self.add('/Type/Pages/MediaBox[0 0 %d %d]/Count 1/Kids[3 0 R]' % (self.pw, self.ph))
        fonts = '/Font<<' + ''.join(['/F%d %d 0 R' % (f, i+4)  for i,f in enumerate(ft)]) + '>>'
        self.add('/Type/Page/Parent 2 0 R/Resources<<%s>>/Contents %d 0 R' % (fonts, len(ft)+4))
        enc = '/Encoding<</Type/Encoding/Differences[1 %s]>> ' % __e__
        for f in ft: self.add('/Type/Font/Subtype/Type1/BaseFont/%s %s' % (__fonts__[f-1], enc))
        o, urlink = b'', []
        for (pa, pc, gr, rect) in pages: o += gr + self.ctext(pc, rect) + self.ltext(pa, rect)
        self.addstream(o)
        size = self.addref()
        return self.o + bytes('startxref %s\n' % size, 'ascii') + b'%%EOF'

def sanity(s):
    __o__ = r'([çáàâäéèêëíìîïóòôöúùûüŷÿ])'
    return re.sub(__o__, lambda m: r'\%03o' % __o__.index(m.group(1)), s)

def logo(r, c1, c2, x, y):
    return bytes ('q %s rg q %s rg %s 0 0 %s %s %s cm /Im1 Do Q ' % (c1, c2, r, r, x, y), 'ascii')

def img(ratio, x, y):
    return bytes ('q %s 0 0 %s 0 0 cm q 630 0 0 864 %s %s cm /Im2 Do Q Q ' % (ratio, ratio, x, y), 'ascii')

def gen_pdf(t):
    a, color, c1, c2, c3 = pdf(595, 841), (.8,.7,.3), '0 .3 .7', '.3 .3 .3', '.2 .6 .1'
    p = []
    for i in range(len(t)):
        for j in range(len(t[i])):
            xpos, ypos = 40+68*j, 245+12*i
            if j == 2: xpos-=5
            elif j == 3: xpos-=25
            elif j == 4: xpos-=10
            elif j == 5: xpos+=10
            dsp = '%7.2f \001' % t[i][j] if j==7 else '%07d Wh' % t[i][j] if j==6 else '%s' % datetime.timedelta(seconds = t[i][j]) if j==5 else t[i][j]
            p.append((xpos, ypos, 1, 8, dsp))
                   
    header_page = [(300, 50, 5, 24, 'Facture'),
                   (490, 40, 8, 12, '15/09/2015'),
                   (24, 180, 5, 10, 'Ref:'),
                   (50, 180, 8, 10, 'AG-PLG-201601010001'),
                   (40, 220, 1, 12, 'Borne'),
                   (100, 220, 1, 12, 'Utilisateur'),
                   (168, 220, 1, 12, 'Groupe'),
                   (224, 220, 1, 12, sanity('Début')),
                   (312, 220, 1, 12, 'Fin'),
                   (387, 220, 1, 12, sanity('Durée')),
                   (430, 220, 1, 12, 'Consommation'),
                   (520, 220, 1, 12, 'Prix')]
                   

    y, dt, ct, pt = 255+12*len(t), sum([x[5] for x in t]), sum([x[6] for x in t]), sum([x[7] for x in t]) 
    ddisp = datetime.timedelta(seconds = dt)
    foot_page = [(40, y, 1, 12, 'Total'), (388,  y, 5, 9, '%s' % ddisp),(444,  y, 5, 9, '%8d Wh' % ct), (516,  y, 5, 10, '%7.2f \001' % pt)]
    
    colored_page = [(10, 70, 1, 76, c3, 'MON'),
                    (12, 110, 1, 60, c3, 'LOGO'),
                    (360, 120, 5, 16, c1, 'Pluggle S.A.S.'),
                    (360, 140, 1, 12, c1, 'Service Facturation'),
                    (360, 156, 1, 12, c1, '2 bis avenue de MONS'),
                    (360, 172, 1, 12, c1, sanity('31280 Drémil-Lafage')),
                    (60, 820, 1, 6, c2, 'XXXXXXXX SAS Adresse Tel Email TVA FR11000000000 RCS Toulouse'),
                    (86,  730, 1, 96, 3, sanity('Publicité'))]
    graph = b'40 612 m 555 612 l S '
    #graph += bytes('40 %d m 555 %d l S ' % (600-12*len(t), 600-12*len(t)), 'ascii')
    pages = ((header_page + p + foot_page, colored_page, graph, (0, 841)),)
    return a.gen(pages) 

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
    #return b2i(hashlib.sha256(b''.join(tab)).digest()) 
    return int(hashlib.sha256(b''.join(tab)).hexdigest(), 16)

def datencode(n=0):
    "4 chars (minute precision)"
    return i2b(int(time.mktime(time.gmtime())/60 + 60*24*n), 4)

def datdecode(tt):
    "4 chars (minute precision)"
    return time.strftime('%d/%m/%y %H:%M', time.localtime(float(b2i(tt)*60)))

def secencode():
    "4 chars (seconde precision)"
    return i2b(int(time.mktime(time.gmtime())), 4)

def secdecode(tt):
    "4 chars (seconde precision)"
    return time.strftime('%d/%m/%y %H:%M:%S', time.localtime(float(b2i(tt))))

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

    def verify(self, sig, data):
        r, s, G, n = b2i(sig[:66]), b2i(sig[66:]), self.pkgenerator, self.pkorder
        if r < 1 or r > n-1 or s < 1 or s > n-1: return False
        c = inverse_mod(s, n)
        u1, u2 = (H(data) * c) % n, (r * c) % n
        z = u1 * G + u2 * self.pt
        return z.x % n == r

def inverse_mod2(a, m):
    if a < 0 or m <= a: a = a % m
    c, d = a, m
    uc, vc, ud, vd = 1, 0, 0, 1
    while c != 0:
        q, c, d = divmod(d, c) + (c,)
        uc, vc, ud, vd = ud - q*uc, vd - q*vc, uc, vc
    if ud > 0: return ud
    else: return ud + m

def inverse_mod1(a, m):
    return pow(a, m-2, m)

def inverse_mod(a, m):
    return gmpy2.invert(a, m)

##### API #####

def send_post(host='localhost', data=''):
    "_"
    co, serv = http.client.HTTPConnection(host), '/ef/' 
    co.request('POST', serv, data)
    return co.getresponse().read() #.decode('ascii')    

def send_get(host='localhost', data=''):
    "_"
    co = http.client.HTTPConnection(host)
    co.request('GET', '/ef/?' + urllib.parse.quote(data))
    return co.getresponse().read()    

##### WEB APP #####

def update_blc(d):
    "€f for checking"
    dtrx, b, o, k = ropen(d['trx']), {}, 'ok', ecdsa()
    for t in [x for x in dtrx.keys() if len(x) == 13 and len(dtrx[x]) == 150]:
        src, dst, v, msg, sig, dpub = t[4:], dtrx[t][:9], b2i(dtrx[t][9:11]), t + dtrx[t][:14], dtrx[t][-132:], ropen(d['pub'])
        k.pt = Point(c521, b2i(dpub[src][:66]), b2i(dpub[src][66:]+src))
        dpub.close()
        if k.verify(sig, msg): b[src], b[dst] = b[src] - v if src in b else (-v), b[dst] + v if dst in b else v
    dtrx.close()
    dblc = wopen(d['blc'])
    for x in b:
        if x in dblc and b[x] != int(dblc[x]): 
            merr = ' diff %d %s for %s\n' % (b[x], dblc[x], x)
            sys.stderr.write(merr)
            o = merr
            dblc[x] = '%d' % b[x]
    dblc.close()
    return o

def update_ubl(env, d):
    "cup for checking"
    dtrx, b, k, o = ropen(d['trx']), {}, ecdsa(), 'ok'
    for t in filter(lambda x:len(x) == 10, dtrx.keys()):
        n, b[t] = len(dtrx[t])//10, 0
        for i in range(n):
            s = dtrx[t][10*(n-i-1):10*(n-i)]
            digs = ropen(d['igs'])
            if s in digs and reg(re.match(r'([^/]+)/(\S+)$', digs[s].decode('utf8'))): b[t] += ubl(env, reg.v.group(2), t[1:])
            digs.close()
    for t in [x for x in dtrx.keys() if len(x) == 13 and len(dtrx[x]) == 143]:
        src, dst, v, msg, sig, dpub = t[4:], dtrx[t][:9], b2i(dtrx[t][9:11]), t + dtrx[t][:11], dtrx[t][-132:], ropen(d['pub'])
        k.pt, tsrc, tdst = Point(c521, b2i(dpub[src][:66]), b2i(dpub[src][66:]+src)), b'@' + src, b'@' + dst
        dpub.close()
        if k.verify(sig, msg): b[tsrc], b[tdst] = b[tsrc] - v if tsrc in b else (-v), b[tdst] + v if tdst in b else v
    dtrx.close()
    dblc = wopen(d['blc'])
    sys.stderr.write('%s\n' % b)
    for x in b:
        if x in dblc and b[x] != int(dblc[x]): 
            merr = ' diff %d %s for %s\n' % (b[x], dblc[x], x)
            sys.stderr.write(merr)
            o = merr
        dblc[x] = '%d' % b[x]
    dblc.close()
    return o

def update_cup(d, figs, po, ko, p, k):
    "update cup balances after a purchase"
    ig, l = open(figs, 'rb').read(), {}
    s, a = b2i(ig[6:14]), b2i(ig[26:28])
    assert a == 1 # temporary
    i, pu, pi = (len(ig)-28-142*a-s)//167, b2i(ig[14:18]), b2i(ig[18:26])
    if i == 1: icm = k*p + (i-k)*(p-1)
    else: icm = k*p + (i-k)*(p-1) - ko*po - (i-1-ko)*(po-1)
    iga = ig[28:37] # if a == 1 !!!!!!
    if icm != 0: l[iga] = icm
    for j in range(1, i):
        rfd, igb = (po if j<=ko else po-1) - (p if j<=k else p-1), ig[142*a+s+167*j-135:142*a+s+167*j-126]
        if rfd != 0: l[igb] = l[igb] + rfd if igb in l else rfd
    prc, igp = p if k==i else p-1, ig[142*a+s+167*i-135:142*a+s+167*i-126]
    if prc != 0: l[igp] = l[igp] - prc if igp in l else -prc
    dblc = wopen(d['blc'])
    for c in l: dblc[b'@'+c] = '%d' % ((int(dblc[b'@'+c])+l[c]) if b'@'+c in dblc else l[c]) 
    dblc.close()

def nbt(d, cm):
    "get total transaction nb"
    dtrx, n = ropen(d['trx']), 0
    if cm in dtrx: n = len(dtrx[cm])//13
    dtrx.close()
    return n

def blc(d, cm, cup=False):
    "get balance"
    tg = b'@'+cm if cup else cm
    dblc, bal = ropen(d['blc']), 0
    if tg in dblc: bal = int(dblc[tg])
    dblc.close()
    return bal

def tublc(env, d, cm):
    "total cup balance"
    dtrx, bl, tg = ropen(d['trx']), 0, b'@'+cm
    if tg in dtrx:
        n = len(dtrx[tg])//10
        for i in range(n):
            s = dtrx[tg][10*(n-i-1):10*(n-i)]
            digs = ropen(d['igs'])
            if s in digs and reg(re.match(r'([^/]+)/(\S+)$', digs[s].decode('utf8'))): bl += ubl(env, reg.v.group(2), cm)
            digs.close()
    dtrx.close()
    return bl

def debt(d, cm, cut=False):
    "get max debt"
    dcrt, dbt = ropen(d['crt']), 0
    if cm in dcrt and len(dcrt[cm]) == 141: 
        dat, msg, sig, k, p = dcrt[cm][:4], cm + dcrt[cm][:9], dcrt[cm][-132:], ecdsa(), b64tob(bytes(_ibank_pkey + _ibank_id, 'ascii'))
        k.pt = Point(c521, b2i(p[:66]), b2i(p[66:]))
        if is_future(dat) and (cut or k.verify(sig, msg)): dbt = b2i(dcrt[cm][4:9])
    dcrt.close()
    return dbt

def nbig(d, cm):
    "total nb of igs"
    dtrx, tg = ropen(d['trx']), b'@'+cm
    n = len(dtrx[tg])//10 if tg in dtrx else 0
    dtrx.close()
    return n

def ubl(env, url, cm):
    "cup balance"
    figs, bl = '/%s/%s_%s/igf/%s.igf' % (__app__, __app__, env['SERVER_PORT'], url), 0      
    if os.path.isfile(figs):
        ig, rat, sumr = open(figs, 'rb').read(), {}, 0
        s, a = b2i(ig[6:14]), b2i(ig[26:28])
        b, pu, pi = (len(ig)-28-142*a-s)//167, b2i(ig[14:18]), b2i(ig[18:26])
        if b == 0: return 0
        p, k =  b2i(ig[-8:-4]), b2i(ig[-4:])
        for i in range(a):
            ida = ig[28+10*i:37+10*i]
            rat[ida] = b2i(ig[37+10*i:38+10*i])
            sumr += rat[ida]
        bl = sum([int(k*p+(b-k)*(p-1)/rat[x]*sumr) for x in filter(lambda y:y == cm, rat)])
        bl += sum([-p if i<k else 1-p for i in filter(lambda j:ig[32+142*a+s+167*j:41+142*a+s+167*j] == cm, range(b))])
    return bl

def posubl(env, url, cm):
    "cup positions"
    figs = '/%s/%s_%s/igf/%s.igf' % (__app__, __app__, env['SERVER_PORT'], url)   
    if os.path.isfile(figs):
        ig = open(figs, 'rb').read()
        s, a = b2i(ig[6:14]), b2i(ig[26:28])
        b = (len(ig)-28-142*a-s)//167
        for i in range(a):
            if ig[28+10*i:37+10*i] == cm: return 'x %d' % b
        for i in range(b):
            oft = 142*a+s+167*i
            if cm == ig[32+oft:41+oft]: return '%s (%d)' % (datdecode(ig[28+oft:32+oft]), i+1)

def refubl(env, url, cm):
    "cup reference"
    figs = '/%s/%s_%s/igf/%s.igf' % (__app__, __app__, env['SERVER_PORT'], url)
    if os.path.isfile(figs):
        ig, rat, sumr = open(figs, 'rb').read(), {}, 0
        s, a = b2i(ig[6:14]), b2i(ig[26:28])
        for i in range(a):
            ida = ig[28+10*i:37+10*i]
            rat[ida] = b2i(ig[37+10*i:38+10*i])
            sumr += rat[ida]
        if cm in rat: return '%s_%03d%%' % (btob64(cm)[:1], rat[cm]*100//sumr)
        for i in range((len(ig)-28-142*a-s)//167):
            ofst = 142*a+s+167*i
            if cm == ig[32+ofst:41+ofst]: return '%s_%05d' % (btob64(cm)[:1], b2i(ig[41+ofst:43+ofst]))

def curpkn(fig):
    "current p/k/n"
    if os.path.isfile(fig): 
        ig = open(fig, 'rb').read()
        s, a = b2i(ig[6:14]), b2i(ig[26:28])
        b, pu, pi = (len(ig)-28-142*a-s)//167, b2i(ig[14:18]), b2i(ig[18:26])
        p, k = cupprice(pu, pi, b+1, b2i(ig[-8:-4]) if b>0 else pu, b2i(ig[-4:]) if b>0 else 1)
        return (p, k, b+1)
    return 0, 0, 0

def curinfo(fig):
    "current p/k/n"
    if os.path.isfile(fig): 
        ig = open(fig, 'rb').read()
        s, a = b2i(ig[6:14]), b2i(ig[26:28])
        b, pu, pi = (len(ig)-28-142*a-s)//167, b2i(ig[14:18]), b2i(ig[18:26])
        p, k = cupprice(pu, pi, b+1, b2i(ig[-8:-4]) if b>0 else pu, b2i(ig[-4:]) if b>0 else 1)
        prc = p if k==b+1 else p-1 
        return (pu, pi, a, b, prc)
    return 0, 0, 0, 0, 0

def igregister(env, d, url):
    "register new ig"
    figf, lurl = '/%s/%s_%s/igf/%s.igf' % (__app__, __app__, env['SERVER_PORT'], url), '%s/%s' % (env['SERVER_NAME'], url)
    if os.path.isfile(figf):
        igh, ig, dtrx = hashlib.sha1(lurl.encode('utf8')).digest()[:10], open(figf, 'rb').read(), wopen(d['trx'])
        digs = wopen(d['igs'])
        digs[igh] = lurl.encode('utf8')
        digs.close()
        for i in range(b2i(ig[26:28])):
            tg = b'@' + ig[28+10*i:37+10*i]
            if tg in dtrx:
                if igh not in {dtrx[tg][i:i+10]:True for i in range(0, len(dtrx[tg]), 10)}:
                    dtrx[tg] += igh 
            else:
                dtrx[tg] = igh
        dtrx.close()
    return 'ok'    

def is_mairie(d, cm, cut=False):
    "_"
    dcrt, res = ropen(d['crt']), False
    if cm in dcrt and len(dcrt[cm]) == 136: 
        dat, msg, sig, k, p = dcrt[cm][:4], cm + dcrt[cm][:4], dcrt[cm][-132:], ecdsa(), b64tob(bytes(_admin_pkey + _admin_id, 'ascii'))
        k.pt = Point(c521, b2i(p[:66]), b2i(p[66:]))
        if is_future(dat) and (cut or k.verify(sig, msg)) : res = True
    dcrt.close()
    return res

def is_principal(d, cm, cut=False):
    "_"
    dcrt, res = ropen(d['crt']), False
    if cm in dcrt and len(dcrt[cm]) == 145:
        dat, msg, adm, sig, k = dcrt[cm][:4], cm + dcrt[cm][:13], dcrt[cm][4:13], dcrt[cm][-132:], ecdsa()
        if is_mairie(d, adm, cut):
            dpub = ropen(d['pub'])
            k.pt = Point(c521, b2i(dpub[adm][:66]), b2i(dpub[adm][66:]+adm))
            dpub.close()
            if is_future(dat) and (cut or k.verify(sig, msg)) : res = True
    dcrt.close()
    return res

def get_type(d, src):
    dbt, un = debt(d, src, True), '<euro>&thinsp;€</euro>'
    return 'Principal' if is_principal(d, src, True) else 'Mairie' if is_mairie(d, src, True) else '' if dbt == 0 else '%d%s' % (dbt, un)

def init_dbs(dbs, port):
    "_"
    di = '/%s/%s_%s' % (__app__, __app__, port)
    if not os.path.exists(di): os.makedirs(di)
    for dbn in dbs:
        db = '%s/%s' % (di, dbn)
        if not (os.path.isfile(db) or os.path.isfile(db+'.db')):
            d = wopen(db)
            d.close()
            os.chmod(db, 511)
    return {b:'%s/%s' % (di, b) for b in dbs}

def ropen(d):
    return dbm.open(d)

def wopen(d):
    return dbm.open(d, 'c')

def set_crt(d, k, v):
    dcrt = wopen(d['crt'])
    dcrt[k] = v 
    dcrt.close()
    return 'ok'

def app_update():
    "_"
    cd = 'cd %s; git pull origin' % os.path.dirname(os.path.abspath(__file__))
    out, err = subprocess.Popen((cd), shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE).communicate()
    return '%s\n' % err.decode('utf8') if err else 'Message:%s\n' % out.decode('utf8')

def capture_id(d, arg):
    "_"
    dpub = ropen(d['pub'])
    res = [btob64(u) for u in filter(lambda i:re.match(arg, btob64(i)), dpub.keys())]
    dpub.close()
    if len(res) == 1: return res[0]
    return ''

def header():
    return '<?xml version="1.0" encoding="utf8"?>\n<html>\n<meta name="viewport" content="width=device-width, initial-scale=1"/>'

def title():
    return '<a href="./"><img title="Eurofranc 2015, pour l\'économie réelle !" src="%s" width="48"/></a>\n' % (get_image('logo.png'))

def get_image(img):
    "_"
    here = os.path.dirname(os.path.abspath(__file__))
    return 'data:image/png;base64,%s' % base64.b64encode(open('%s/%s' % (here, img), 'rb').read()).decode('ascii')

def getimg(img):
    "_"
    return 'data:image/png;base64,%s' % base64.b64encode(open(img, 'rb').read()).decode('ascii')

def style_html():
    "_"
    o = '<style type="text/css">@import url(http://fonts.googleapis.com/css?family=Schoolbell);h1,h2,p,li,i,b,a,div,input,td,th,footer,svg{font-family:"Lucida Grande", "Lucida Sans Unicode", Helvetica, Arial, Verdana, sans-serif}a.mono,p.mono,td.mono,b.mono{font-family:"Lucida Concole",Courier;font-weight:bold}a.name{margin:50}a{color:DodgerBlue;text-decoration:none}p.alpha{font-family:Schoolbell;color:#F87217;font-size:26pt;position:absolute;top:115;left:80}div.qr,a.qr{position:absolute;top:0;right:0;margin:15}p.note{font-size:9}p.msg{font-size:12;position:absolute;top:0;right:120;color:#F87217}p.stat{font-size:9;position:absolute;top:0;right:20;color:#999}input{font-size:28;margin:3}input.txt{width:210}input.digit{width:120;text-align:right}input.simu{width:120;text-align:right}input[type=checkbox]{width:50}input[type=submit]{color:white;background-color:#AAA;border:none;border-radius:8px;padding:3}p,li{margin:10;font-size:18;color:#333}b.red,td.red{color:red}b.green{color:green}b.blue{color:blue}b.bigorange{font-size:32;color:#F87217}b.biggreen{font-size:32;color:green}td.smallgreen{font-size:9;color:green}b.huge{position:absolute;top:15;left:76;font-size:90;}#wrap{overflow:hidden}a.ppc{font-weight:bold;font-size:.9em}a.ppc:after{font-weight:normal;content:"Cash"}#lcol{float:left;width:360;padding:4}#rcol{margin-left:368;padding:4}footer{bottom:0;color:#444;font-size:10;padding:4}table{margin:1;border:2px solid #999;border-collapse:collapse; background-color:white; opacity:.7}td,th{font-size:11pt;border:1px solid #666;padding:2pt}th{background-color:#DDD}td.num{font-size:12;text-align:right}#c1{float:left;width:23%;padding:1%}#c2{float:left;width:23%;padding:1%}#c3{float:left;width:23%;padding:1%}#c4{float:left;width:23%;padding:1%}h1{color:#888;font-size:25;margin:10 0 0 6}h2{color:#AAA;font-size:18;margin:5 0 0 30}svg{background-color:white}img.book{border:2px outset}text{font-size:18pt}body{margin:0}euro:after{font-size:60%;vertical-align:30%;content:"f"}img{vertical-align:middle}p.address{position:relative;left:380;color:blue}'
    return o + '</style>'

def favicon():
    "_"
    return '<link rel="shortcut icon" type="www/image/png" href="data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAMAAAAoLQ9TAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAgY0hSTQAAeiYAAICEAAD6AAAAgOgAAHUwAADqYAAAOpgAABdwnLpRPAAAAXFQTFRF/wCA/wOC/wF//wB5/wB3/wB+/wKB/wqD/0Cg/1+v/z+g/wqF/wWC/wSC/1ms/+Px//////7///v9/2e0/wB0/wR4/wB1/wB8/wCB/wB4/2qz/+32/7fb/7nc//r9/zmb/xiL/4XC/5bL/y6X/wB7/yOP//L4/8fj/xaL/x+P/xKH/9Lp/+Ty/0ul/4LB//3+/ziZ/wmF/7ze/wJ//wB6/6/X//b7//j8//X6/w+I/zOZ/9/v/9rs/0mk/0ym/0um/02m/1ut/222/9Xq/1Kp/weE/wB//wB9/2Gw//D3/+by/ofD/onE/4zG/4fD/wp9/xB//7jZ/wBw/wOB/4/H/c/m/M3l/77f/wuF/7rc/wSD/wBx/3W3/ziV/wBu/wN7/wF6/xOG//3//7Xa/x2N/+v1/9Lo/ySS/yuW/1Co/7rd/1ys//H4/8Lh/8Ph/3y+/3a7/2az/wGB/06m/9zu//z+/wBv/wR7/weB/zmd/1SqcikTHwAAAAFiS0dEEJWyDSwAAAAJcEhZcwAACxMAAAsTAQCanBgAAADvSURBVBjTY2AAAkYmZhYWZlYGGGBjZufg5OTiZuDhZYPw+fgFBIUEhEVExcQlgOolpQQEpGVk5eQVFJWUxRnYVFTVBNQ1JJk1tbQFdHSZGXiZ9QT0DZi5DcUVBIxYjBkYTEwF9PXNhMzNzSz0BfgtWRlYrawFbGzt7B0cnQScXVzdGNw9PAW8vH18/fwDBAKDghkYVEIsBIRCw5zDIzQEIlWAAlHRMQKCsXHxCZKJScnMQAE21pRUgbR0cfeMTPMskADQYdkCAjm5eQL5BYXiRRCnF5cICJYKeJSVS8A8V1FZ5aLMxssI8y7Y+yYQNgBQWiTEKkSv3QAAACV0RVh0ZGF0ZTpjcmVhdGUAMjAxNC0wNS0yNlQxMDozMDoxMCswMjowMP2x9zQAAAAldEVYdGRhdGU6bW9kaWZ5ADIwMTQtMDUtMjZUMTA6MzA6MTArMDI6MDCM7E+IAAAAAElFTkSuQmCC"/>'

def footer():
    "_"
    return '<footer>Contact: <a href="mailto:%s">%s</a><br/><a href="http://cupfoundation.net">⊔FOUNDATION</a> is registered in Toulouse/France SIREN: 399 661 602 00025</footer></html>' % (__email__, __email__)

def app_index(d, env):
    o = header() + favicon() + style_html() + title()
    o += '<p><b class="green">Si vous désirez tester gratuitement l\'application <i>iOS</i>, envoyez nous votre adresse e-mail d\'<i>AppleID</i> et installez <a href="https://www.testflightapp.com">TestFlight</a> sur votre iPhone sous <i>iOS8</i></b></p>'
    o += '<p><a href="./?users">Users</a> | <a href="./?transactions">Transactions</a> | <a href="./?igs">Intangible-goods</a> | <a href="./?rates">%s</a></p>' % rates('/%s/%s_%s/rates' % (__app__, __app__, env['SERVER_PORT']), True)
    o += '<p><i>Consultez un compte</i><form method="post"><input class="txt" title="code \'MOI\' de 18 caractères alphanumérique affiché en haut du téléphone" pattern="\S+" required="yes" name="cm" placeholder="...€f-ID"/><input title="@nom-public-Twitter ou alias-privé-local" class="txt" pattern=".+" required="yes" name="alias" placeholder="@... (Twitter)"/><input type="submit" value="ok"/></form></p>\n'
    if 'HTTP_COOKIE' in env:
        for x in env['HTTP_COOKIE'].split(';'):
            t = x.split('=')
            cm = b64tob(bytes(t[1], 'ascii'))
            al = urllib.parse.unquote(t[0])
            fc = '/%s/%s_%s/img/%s.png' % (__app__, __app__, env['SERVER_PORT'], t[1])
            img = getimg(fc) if os.path.isfile(fc) else get_image('user48.png')
            o += '<p><a href="./%s" title="%s"><img src="%s"/>%s</a></p>' % (t[1], t[1], img, al)
        o += '<p><form method="post"><input type="submit" name="rem" value="Effacer les cookies"/></form></p>\n'
    return o + footer()

def app_users(d, env):
    o, un = header() + favicon() + style_html(), '<euro>&thinsp;€</euro>'
    dpub, dblc = ropen(d['pub']), ropen(d['blc'])
    o += '<table><tr><td>%s</td><td class="num">%d users</td><td><a href="./?transactions" class="num">transactions</a></td><td><a href="./?igs" class="num">intangible-goods</a></td></tr></table><table>' % (title(), len(dpub.keys()))
    for i, src in enumerate(dpub.keys()): 
        fc = '/%s/%s_%s/img/%s.png' % (__app__, __app__, env['SERVER_PORT'], btob64(src))
        img = getimg(fc) if os.path.isfile(fc) else get_image('user48.png')
        #blcup = tublc(env, d, src)
        #blef = int(dblc[src])/100 if src in dblc else 0
        o += '<tr><td class="num">%d</td><td><img width="24" src="%s"/></td><td><a href="./%s" class="mono">%s</a></td><td class="num">%s</td><td class="num">%04d</td><td class="num">%7.2f%s</td><td class="num">%7d&thinsp;⊔</td></tr>' % (i+1, img, btob64(src), btob64(src), get_type(d, src), nbt(d, src), blc(d, src)/100, un, blc(d, src, True))
    dpub.close()
    dblc.close()
    return o + '</table>' + footer()

def app_invoice(d, env):
    o, un, dat, tot = header() + favicon() + style_html(), '<euro0>&thinsp;€</euro0>', '%s' % datetime.datetime.now(), 0
    dobj = ropen(d['obj'])
    o += '<right><h1>Facture</h1></right>'
    o += '<h2>%s</h2>' % dat[:-16]
    o += '<p class="address"><b>PluggleS.A.S.</b><br/><small><i>Service facturation</i><br/>2 bis avenue de Mons<br/>31280 Drémil-Lafage<br/>France<small></p>'
    o += '<p><i>Ref:</i>CUSTOMER020150901</p>'
    o += '<table><tr><th></th><th>Borne</th><th>Utilisateur</th><th>Groupe</th><th>Début</th><th>Fin</th><th>Durée</th><th>Prix</th></tr>' 
    tmp = [ b2i(t) for t in filter(lambda x:len(x) == 4, dobj.keys())]
    for i, z in enumerate(sorted(tmp)):
        t = i2b(z)
        dur = b2i(dobj[t]) - b2i(t)
        delta, prc = datetime.timedelta(seconds = dur), dur*0.0054
        o += '<tr><td class="num">%d</td><td>201505180002</td><td>ZqYajTFslP</td><td>EmployéT1</td><td>%s</td><td>%s</td><td class="num">%s</td><td class="num">%7.2f%s</td></tr>' % (i+1, secdecode(t), secdecode(dobj[t]), delta, prc, un)
        tot += prc
    dobj.close()
    o += '<tr><th></th><th colspan="6">Total</th><th class="num">%7.2f%s</th></tr>' %(tot,un)
    o += '</table>'      
    return o 


def app_invoicePDF(d, env):
    dobj, t2 = ropen(d['obj']), []
    tmp = [ b2i(t) for t in filter(lambda x:len(x) == 4, dobj.keys())]
    for i, z in enumerate(sorted(tmp)):
        t = i2b(z)
        dur = b2i(dobj[t]) - b2i(t)
        t2.append(['201505180002', 'ZqYajTFslP', 'Empl_T1', '%s' % secdecode(t), '%s' % secdecode(dobj[t]), dur, dur*1.5, dur*0.0054])
    dobj.close()
    return gen_pdf(t2)

def app_clean(d, env):
    dobj = wopen(d['obj'])
    for x in dobj.keys(): del dobj[x]
    dobj.close()
    return 'cleaned'

def app_trx(env, d):
    o, un, uc, i = header() + favicon() + style_html(), '<euro>&thinsp;€</euro>', '&thinsp;⊔', 0
    dtrx = ropen(d['trx'])
    tab = [z for z in filter(lambda x:(len(x) == 13) or (len(x) == 10), dtrx.keys())]
    o += '<table><tr><td>%s</td><td><a href="./?users" class="num">users</a></td><td class="num">%d transactions</td><td><a href="./?igs" class="num">intangible-goods</a></td></tr></table><table>' % (title(), len(tab)) 
    for i, t in enumerate(filter(lambda x:len(x) == 13, dtrx.keys())):
        if len(dtrx[t]) == 150: 
            prf = btob64(t[4:])[:1] + btob64(dtrx[t][:9])[:1]
            o += '<tr><td class="num">%d</td><td class="num">%s</td><td><a href="./%s" class="mono">%s</a></td><td><a href="%s" class="mono">%s</a></td><td class="mono smallgreen">%s%07d</td><td class="num">%7.2f%s</td></tr>' % (i+1, datdecode(t[:4]), btob64(t[4:]), btob64(t[4:]), btob64(dtrx[t][:9]), btob64(dtrx[t][:9]), prf, b2i(dtrx[t][11:14]), b2i(dtrx[t][9:11])/100, un)
        elif len(dtrx[t]) == 143:
            o += '<tr><td class="num">%d</td><td class="num">%s</td><td><a href="./%s" class="mono">%s</a></td><td><a href="%s" class="mono">%s</a></td><td class="mono smallgreen">iBank</td><td class="num">%7d&thinsp;⊔</td></tr>' % (i+1, datdecode(t[:4]), btob64(t[4:]), btob64(t[4:]), btob64(dtrx[t][:9]), btob64(dtrx[t][:9]), b2i(dtrx[t][9:11]))
    j = i+1
    for t in filter(lambda x:len(x) == 10, dtrx.keys()):
        n = len(dtrx[t])//10
        for i in range(n):
            s = dtrx[t][10*(n-i-1):10*(n-i)]
            digs = ropen(d['igs'])
            if s in digs:
                url = digs[s].decode('utf8')
                if reg(re.match(r'([^/]+)(/\S+)$', url)):
                    dat, ref = posubl(env, reg.v.group(2), t[1:]), refubl(env, reg.v.group(2), t[1:])
                    o += '<tr><td class="num">%d</td><td class="num">%s</td><td><a href="./%s" class="mono">%s</a></td><td><a href="http://%s?:" class="num">%s</a></td><td class="mono smallgreen">%s</td><td class="num">%7d&thinsp;⊔</td></tr>' % (j+1, dat, btob64(t[1:]), btob64(t[1:]), url, url, ref, ubl(env, reg.v.group(2), t[1:]))
                    j += 1
            digs.close()
    dtrx.close()
    return o + '</table>' + footer()

def app_igs(env, d):
    o, un, uc = header() + favicon() + style_html(), '<euro>&thinsp;€</euro>', '&thinsp;⊔'
    digs = ropen(d['igs'])
    o += '<table><tr><td>%s</td><td><a href="./?users" class="num">users</a></td><td><a href="./?transactions" class="num">transactions</td><td class="num">%d intangible-goods</a></td></tr></table><table>' % (title(), len(digs.keys())) 
    for i, ig in enumerate(digs.keys()):
        url = digs[ig].decode('utf8')
        if reg(re.match(r'([^/]+)(/\S+)$', url)):
            figf = '/%s/%s_%s/igf/%s.igf' % (__app__, __app__, env['SERVER_PORT'], reg.v.group(2))
            [pu, pi, a, n, prc]  = curinfo(figf)
            sdisp, bdisp = 'sellers' if a>1 else 'seller', 'buyers' if n>1 else 'buyer'
            o += '<tr><td class="num">%d</td><td class="num">%d %s -> %d %s</td><td class="num">init-price: %d&thinsp;⊔</td><td class="num">expected-income: %d&thinsp;⊔</td><td><a href="http://%s?:" class="num">%s</a></td><td class="num">%7d&thinsp;⊔</td></tr>' % (i+1, a, sdisp, n, bdisp, pu, pi, url, url, prc)
    digs.close()
    return o + '</table>' + footer()

def app_report(d, src, env):
    o, un, r = header() + favicon() + style_html(), '<euro>&thinsp;€</euro>', b64tob(bytes(src, 'ascii'))
    dtrx, dblc, tg = ropen(d['trx']), ropen(d['blc']), b'@' + r    
    fc = '/%s/%s_%s/img/%s.png' % (__app__, __app__, env['SERVER_PORT'], src)
    img = getimg(fc) if os.path.isfile(fc) else get_image('user48.png')
    bl = blc(d, r, True)
    o += '<table><tr><td>%s</td><td class="mono"><img src="%s"/> %s</td><td class="num">%s</td><td class="num red">%7.2f%s</td><td class="num red">%7d&thinsp;⊔</td></tr></table><table>' % (title(), img, src, get_type(d, r), int(dblc[r])/100 if r in dblc else 0, un, bl) 
    dblc.close()
    if tg in dtrx:
        n = len(dtrx[tg])//10
        for i in range(n):
            s = dtrx[tg][10*(n-i-1):10*(n-i)]
            digs = ropen(d['igs'])
            url = 'none' if s not in digs else digs[s].decode('utf8')
            digs.close()
            if reg(re.match(r'([^/]+)(/\S+)$', url)):
                bl, pos, ref = ubl(env, reg.v.group(2), r), posubl(env, reg.v.group(2), r), refubl(env, reg.v.group(2), r)
                o += '<tr><td class="num">%03d</td><td class="num">%s</td><td><a href="%s" class="num">%s</a></td><td class="mono smallgreen">%s</td><td class="num">%7d&thinsp;⊔</td></tr>' % (n-i, pos, url, url, ref, bl)
    if r in dtrx:
        n = len(dtrx[r])//13
        for i in range(n):
            s = dtrx[r][13*(n-i-1):13*(n-i)]
            if len(dtrx[s]) == 150:
                (w, ur) = (i2b(0,1), dtrx[s][:9]) if s[4:] == r else (i2b(1,1), s[4:])
                dst = btob64(ur)
                prf = dst[:1] + src[:1] if b2i(w) == 1 else src[:1] + dst[:1]
                val = b2i(dtrx[s][9:11]) if b2i(w) == 1 else -b2i(dtrx[s][9:11])
                fc = '/%s/%s_%s/img/%s.png' % (__app__, __app__, env['SERVER_PORT'], dst)
                img = getimg(fc) if os.path.isfile(fc) else get_image('user48.png')
                o += '<tr><td class="num">%03d</td><td class="num">%s</td><td><a href="./%s" class="mono"><img width="24" src="%s"/> %s</a></td><td class="mono smallgreen">%s%07d</td><td class="num">%7.2f%s</td></tr>' % (n-i, datdecode(s[:4]), btob64(ur), img, btob64(ur), prf, b2i(dtrx[s][11:14]), val/100, un)
            elif len(dtrx[s]) == 143:
                (w, ur) = (i2b(0,1), dtrx[s][:9]) if s[4:] == r else (i2b(1,1), s[4:])
                dst, val = btob64(ur), b2i(dtrx[s][9:11]) if b2i(w) == 1 else -b2i(dtrx[s][9:11])
                fc = '/%s/%s_%s/img/%s.png' % (__app__, __app__, env['SERVER_PORT'], dst)
                img = getimg(fc) if os.path.isfile(fc) else get_image('user48.png')
                o += '<tr><td class="num">%03d</td><td class="num">%s</td><td><a href="./%s" class="mono"><img width="24" src="%s"/> %s</a></td><td class="mono smallgreen">iBank</td><td class="num">%7d&thinsp;⊔</td></tr>' % (n-i, datdecode(s[:4]), btob64(ur), img, btob64(ur), val)
    dtrx.close()
    return o + '</table>' + footer()

def reg(value):
    " function attribute is a way to access matching group in one line test "
    reg.v = value
    return value

def get_twitter_img(port, user, cm):
    di = '/%s/%s_%s/img' % (__app__, __app__, port)
    fi, fk, fc = '%s/%s.png' % (di, user), '%s/twitter_keys' % di, '%s/%s.png' % (di, cm),
    if not os.path.isfile(fi):
        k = eval(open(fk).read())
        header = requests_oauthlib.OAuth1(k['CK'], k['CS'], k['AK'], k['AS'], signature_type='auth_header')
        tab = requests.get('https://api.twitter.com/1.1/users/show.json?screen_name=' + user, auth = header).json()
        if reg(re.match(r'http://([^/]+)(/\S+)$', tab['profile_image_url'])):
            co = http.client.HTTPConnection(reg.v.group(1))
            co.request('GET', reg.v.group(2))
            open(fi, 'wb').write(co.getresponse().read())
    if not os.path.isfile(fc): os.symlink('%s.png' % user, fc)

def is_future(da):
    return int(time.mktime(time.gmtime())) < b2i(da)*60

def cupprice(pu, pi, i, ko, po):
    "_"
    x = pu + (i-1)*pu//2
    t = x if x<=pi else pi if pu>2 else pu if i<pu else i if i<pi else pi
    for p in range(t//i-2, t//i+2):
        k = t-i*(p-1)
        if k>0 and k<=i and (p!=po or k<=ko or t==pi or p<=1 or k>=i): return p, k

def req_5(r):
    "is active"
    return 'ok' if r == b'ef0.1' else ''

# pluggle (iphone call)
def req_8(d, r):
    "toggle obj"
    dobj, deb = wopen(d['obj']), secencode()
    dobj[r] = b'0' if r in dobj.keys() and dobj[r] == b'1' else b'1'
    if dobj[r] == b'1':
        dobj[b'c'] = deb
    if dobj[r] == b'0' and b'c' in dobj.keys():
        dobj[dobj[b'c']] = deb
    o = dobj[r].decode('ascii')
    dobj.close()
    return o

def req_9(d, r):
    "get balance €f + nb transactions + balance cup + nb igs | src:9"
    o = '%d:%d:%d:%d' % (blc(d, r), nbt(d, r), blc(d, r, True), nbig(d, r))
    return o

# PLUGGLE RPI polling 1Hz
# phone send ON

#
# RPI send date+conso
# web store conso
# web response ON/OFF
# RPI activate/decactivate relay


# pluggle (rpi call)
# send objid:8+ consovalue:8
def req_10(d, r):
    "read obj state"
    dobj = ropen(d['obj'])
    o = dobj[r].decode('ascii') if r in dobj.keys() else '0'
    dobj.close()
    return o

def req_12(d, r):
    "get transaction nb | src:9+pos:3"
    src, pos, dtrx, o, n = r[:9], b2i(r[9:]), ropen(d['trx']), 'error', nbt(d, r[:9])
    if n > 0 and pos >= 0 and pos < n:
        sl = dtrx[src][13*pos:13*(pos+1)]
        (w, ur) = (i2b(0,1), dtrx[sl][:9]) if sl[4:] == src else (i2b(1,1), sl[4:])
        o = btob64(sl[:4] + ur + dtrx[sl][9:14] + w + i2b(n, 2)) 
        # return | dat:4+usr:9+val:2+ref:3+way:1+max:2 len(21->28)
        # QRCODE:15 btob64(dat+usr:12+val)
    dtrx.close()
    return o

def req_15(d, r):
    "check transaction (short) | dat:4+scr:9+val:2"
    u, dat, src, val, dtrx, o = r[:13], r[:4], r[4:13], r[:-2], ropen(d['trx']), 'error'
    if u in dtrx and dtrx[u][9:11] == val: o = '%d:%d' % (b2i(dtrx[u][14:16]), b2i(dtrx[u][16,18]))
    dtrx.close()
    return o

# pluggle (rpi call)
# send objid:8+ consovalue:8
def req_16(d, r):
    "read obj state"
    dobj = ropen(d['obj'])
    o = dobj[r].decode('ascii') if r in dobj.keys() else '0'
    dobj.close()
    return o

def req_24(d, r): 
    "check transaction (long) | dat:4+scr:9+dst:9+val:2"
    u, dst, val, dtrx, o = r[:13], r[13:22], r[:-2], ropen(d['trx']), 'error'
    if u in dtrx and dtrx[u][:9] == dst and dtrx[u][9:11] == val: o = '%d:%d' % (b2i(dtrx[u][14:16]), b2i(dtrx[u][16:18]))
    dtrx.close()
    return o

def req_132(d, r):
    "register publickey | pbk:132 len(132) SPAMING RISK -> SHALL BE REMOVED !"
    pub, src, v, dpub, o = r, r[-9:], r[:-9], wopen(d['pub']), 'error'
    if src in dpub: o = 'old'
    else: dpub[src], o = v, 'new'
    dpub.close()
    return o

def req_145(d, r):
    "admin certificate: usr:9+dat:4+sig:132"
    src, v, dat, msg, sig, k, p, o = r[:9], r[9:], r[9:13], r[:13], r[-132:], ecdsa(), b64tob(bytes(_admin_pkey + _admin_id, 'ascii')), 'error'
    k.pt = Point(c521, b2i(p[:66]), b2i(p[66:]))
    if is_future(dat) and k.verify(sig, msg): o = set_crt(d, src, v)
    return o

def req_147(d, r):
    "admin certificate: usr:9+dat:4+spr:2+sig:132"
    src, v, dat, msg, sig, k, p, o = r[:9], r[9:], r[9:13], r[:15], r[-132:], ecdsa(), b64tob(bytes(_admin_pkey + _admin_id, 'ascii')), 'error'
    k.pt = Point(c521, b2i(p[:66]), b2i(p[66:]))
    if is_future(dat) and k.verify(sig, msg): o = set_crt(d, src, v)
    return o

def req_150(d, r):
    "ibank certificate: bnk:9+dat:4+dbt:5+sig:132"
    src, v, dat, dbt, msg, sig, k, p, o = r[:9], r[9:], r[9:13], b2i(r[13:18]), r[:18], r[-132:], ecdsa(), b64tob(bytes(_ibank_pkey + _ibank_id, 'ascii')), 'error'
    k.pt = Point(c521, b2i(p[:66]), b2i(p[66:]))
    if is_future(dat) and k.verify(sig, msg): o = set_crt(d, src, v)
    return o

def req_154(d, r):
    "user principal certificate (short): usr:9+dat:4+adm:9+sig:132"
    usr, v, dat, adm, msg, sig, k, o = r[:9], r[9:], r[9:13], r[13:22], r[:22], r[-132:], ecdsa(), 'error'
    if is_mairie(d, adm):
        dhid = ropen(d['hid'])
        if adm in dhid: h = dhid[adm][4:36] # next !
        dhid.close()
        dpub = ropen(d['pub'])
        k.pt = Point(c521, b2i(dpub[adm][:66]), b2i(dpub[adm][66:]+adm))
        dpub.close()
        if is_future(dat) and k.verify(sig, msg): o = set_crt(d, usr, v) 
    return o

def req_156(d, r):
    "add ⊔ transaction dat:4+src:9+dst:9+val:2+sig:132"
    u, v, dat, src, dst, val, msg, sig, k, dpub, o = r[:13], r[13:], r[:4], r[4:13], r[13:22], b2i(r[22:24]), r[:-132], r[-132:], ecdsa(), ropen(d['pub']), 'error'
    if src in dpub and dst in dpub and src != dst and val != 0 and (debt(d, src)>0 or debt(d, dst)>0):
        k.pt = Point(c521, b2i(dpub[src][:66]), b2i(dpub[src][66:]+src))
        dpub.close()
        dtrx = wopen(d['trx'])
        if k.verify(sig, msg) and u not in dtrx and blc(d, src, True) + debt(d, src)*100 >= val:
            dtrx[u], dblc, tgsrc, tgdst, o = v, wopen(d['blc']), b'@' + src, b'@' + dst, 'ok'
            dtrx[src], dtrx[dst] = dtrx[src] + u if src in dtrx else u, dtrx[dst] + u if dst in dtrx else u # shortcut
            dblc[tgsrc] = '%d' % ((int(dblc[tgsrc])-val) if tgsrc in dblc else (-val)) # shortcut
            dblc[tgdst] = '%d' % ((int(dblc[tgdst])+val) if tgdst in dblc else val)    # shortcut
            dblc.close()
        dtrx.close()
    return o

def req_159(d, r): 
    "add €f transaction: dat:4+src:9+dst:9+val:2+ref:3+sig:132"
    u, v, dat, src, dst, val, ref, msg, sig, k, dpub, o = r[:13], r[13:-132], r[:4], r[4:13], r[13:22], b2i(r[22:24]), b2i(r[24:27]), r[:-132], r[-132:], ecdsa(), ropen(d['pub']), 'error'
    if src in dpub and dst in dpub and src != dst and val != 0:
        k.pt = Point(c521, b2i(dpub[src][:66]), b2i(dpub[src][66:]+src))
        dpub.close()
        if k.verify(sig, msg): 
            dtrx = wopen(d['trx'])
            if u in dtrx: o = '%d:%d' % (b2i(dtrx[u][14:16]), b2i(dtrx[u][16:18]))
            else:
                if blc(d, src) + debt(d, src)*100 >= val:
                    dtrx[src], dtrx[dst] = dtrx[src] + u if src in dtrx else u, dtrx[dst] + u if dst in dtrx else u # shortcut
                    ps, pd = len(dtrx[src])//13-1, len(dtrx[dst])//13-1
                    dtrx[u], dblc = v + i2b(ps, 2) + i2b(pd, 2) + sig, wopen(d['blc'])
                    dblc[src] = '%d' % ((int(dblc[src])-val) if src in dblc else (-val)) # shortcut
                    dblc[dst] = '%d' % ((int(dblc[dst])+val) if dst in dblc else val)    # shortcut
                    o = '%d:%d' % (ps, pd)
                    dblc.close()
                else: o += ' balance!'
            dtrx.close()
        else: o += ' signature!'
    else: o += ' ids!'
    return o

def req_162(d, r): 
    "add €f pending transaction: dat:4+src:9+dst:9+val:2+ref:5+pnd:1+sig:132"
    pass

def req_186(d, r):
    "user principal certificate: usr:9+dat:4+adm:9:hid:32+sig:132" 
    usr, v, dat, adm, hid, msg, sig, k, h, o = r[:9], r[9:], r[9:13], r[13:22], r[22:54], r[:54], r[-132:], ecdsa(), None, 'error'
    if is_mairie(d, adm):
        dhid = ropen(d['hid'])
        if adm in dhid: h = dhid[adm][4:36]
        dhid.close()
        dpub = ropen(d['pub'])
        k.pt = Point(c521, b2i(dpub[adm][:66]), b2i(dpub[adm][66:]+adm))
        dpub.close()
        if hid == h and is_future(dat) and k.verify(sig, msg): o = set_crt(d, usr, v)
        # maybe re-check register signature !
    return o

def req_300(d, r):
    "register main account: dat:4+hashid:32+pubkey:132+sig:132"
    dat, hid, src, pk1, pk2, v, msg, sig, k, o = r[:4], r[4:36], r[159:168], r[36:102], r[102:168], r[36:159], r[:-132], r[-132:], ecdsa(), 'error'
    k.pt = Point(c521, b2i(pk1), b2i(pk2))
    if k.verify(sig, msg):
        dpub, dhid = wopen(d['pub']), wopen(d['hid'])
        if hid not in dhid: o, dhid[src], dhid[hid] = 'ok', dat + hid + sig, src
        if src not in dpub: dpub[src] = v
        dhid.close()
        dpub.close()
    return o

def buyig(env, d, r, base):
    "_"
    figf, url, o = '/%s/%s_%s/igf/%s.igf' % (__app__, __app__, env['SERVER_PORT'], base), '%s/%s' % (env['SERVER_NAME'], base), 'error'
    src, tg, igh, msg, sig, q, vu = r[4:13], b'@' + r[4:13], hashlib.sha1(url.encode('utf8')).digest()[:10], r[:-132], r[-132:], ecdsa(), False
    if os.path.isfile(figf):
        ig = open(figf, 'rb').read()
        if b2i(ig[4:6]) == 0:
            tg = b'$' + r[4:13] # finir
            return 'cheque'
        s, a = b2i(ig[6:14]), b2i(ig[26:28])
        b = (len(ig)-28-142*a-s)//167
        dpub = wopen(d['pub'])                    
        q.pt = Point(c521, b2i(dpub[src][:66]), b2i(dpub[src][66:]+src))
        dpub.close()
        for i in range(b):
            c = ig[28+142*a+s+167*i:195+142*a+s+167*i] 
            if c[:147] == r: o, vu = btob64(c[4:13] + i2b(i, 6) + c[-20:-8]), True
        [p, k, n]  = curpkn(figf)
        if n != b+1: return 'Error position'
        po, ko = b2i(ig[-8:-4]) if b>0 else b2i(ig[14:18]), b2i(ig[-4:]) if b>0 else 1
        prc = p if k==n else p-1 
        if not vu and blc(d, src, True) + debt(d, src) + 100 > prc:
            if q.verify(sig, msg + i2b(p, 4) + i2b(k, 4) + i2b(n, 4) + base.encode('utf8')):
                dtrx = wopen(d['trx'])
                if tg in dtrx:
                    if igh not in {dtrx[tg][i:i+10]:True for i in range(0, len(dtrx[tg]), 10)}:
                        dtrx[tg] += igh 
                else:
                    dtrx[tg] = igh
                dtrx.close()
                sk = hashlib.sha1(os.urandom(32)).digest()[:12]
                open(figf, 'ab').write(r + sk + i2b(p, 4) + i2b(k, 4))
                update_cup(d, figf, po, ko, p, k)
                o = btob64(src + i2b(b+1, 6) + sk)
            else:
                o += ' signature'
        else:
            o = 'old purchase'
    return o

def readig(env, rk, base):
    "_"
    figf, p = '/%s/%s_%s/igf/%s.igf' % (__app__, __app__, env['SERVER_PORT'], base), b2i(rk[9:15])
    if os.path.isfile(figf): 
        r = open(figf, 'rb').read()
        s, a, t = b2i(r[6:14]), b2i(r[26:28]), len(r)
        if p <= (t-28-142*a-s)//167:
            c = r[28+142*a+s+167*(p-1):28+142*a+s+167*(p)]
            if c[4:13] == rk[:9] and c[-20:-8] == rk[15:]: 
                return r[28+10*a:28+10*a+s]
        return '%d %d' % (a, s)
    return ''


def readforex(db, disp=False):
    dr = dbm.open(db, 'r')
    for i in dr.keys():
        l = eval(dr[i])
        print (i.decode('ascii'), l['EUR'])
    dr.close()

def testforex():
    co, cu = http.client.HTTPConnection('currencies.apps.grandtrunk.net'), datetime.datetime.now()
    cc = '%s' % cu
    co.request('GET', '/getrate/%s/EUR/USD' % (cc[:10]))
    print (cc[:16], float(co.getresponse().read()))
    co.close()
    cu = datetime.datetime(2015, 1, 1)
    while cu < datetime.datetime.now() - datetime.timedelta(days=1):
        cc = '%s' % cu
        print(cc[:10])
        cu += datetime.timedelta(days=1)
        print ('cu ', '%s', cu)


def forex(db, disp=False):
    now, h = '%s' % datetime.datetime.now(), {}
    dr = dbm.open(db, 'c')
    cu, co = datetime.datetime(2014, 1, 1), http.client.HTTPConnection('currencies.apps.grandtrunk.net')
    #del dr['2015-01-13']
    #del dr['2015-01-12']
    while cu < datetime.datetime.now() - datetime.timedelta(days=1):
        cc = '%s' % cu
        if bytes(cc[:10], 'ascii') not in dr:
            for c in filter(lambda i:i!='USD', __curset__):
                if disp:
                    print('grandtrunk request for %s %s' % (c, cc[:10]))                    
                else:
                    sys.stderr.write('grandtrunk request for %s %s\n' % (c, cc[:10]))
                #print('GET', '/getrate/%s/%s/USD' % (cc[:10], c))
                co.request('GET', '/getrate/%s/%s/USD' % (cc[:10], c))
                h[c] = float(co.getresponse().read())
            dr[cc[:10]] = '%s' % h
        cu += datetime.timedelta(days=1)
    co.close()
    dr.close()

def rates(db, dbl=True, all=False):
    "with 5% taxes"
    d, c, o, o1 = dbm.open(db, 'c'), datetime.datetime(2014, 1, 1), '', 'Date            | 5% selling-tax | nominal-rate | 5% buying-tax\n' if all else ''
    x = bytes(('%s' % c)[:10], 'ascii')
    A = eval(d[x].decode('ascii'))
    A['⊔'] = .1*A['EUR']
    while x in d:
        if all: o = '%s: 1⊔ = [%12.10f > %12.10f < %12.10f] €f\n' % (x.decode('ascii'), .95*A['⊔']/A['EUR'], A['⊔']/A['EUR'], 1.05*A['⊔']/A['EUR']) + o
        c += datetime.timedelta(days=1)
        x = bytes(('%s' % c)[:10], 'ascii')
        if x in d:
            B = eval(d[x].decode('ascii'))
            B['⊔'] = delta2(d, A, B) if dbl else delta1(d, A, B) 
            A = B
    d.close()
    return '%s: 1⊔ = %s€f\n' % (x.decode('ascii'), B['⊔']/B['EUR']) + o1 + o

def rates0(db):
    d, c, o = dbm.open(db, 'c'), datetime.datetime(2014, 1, 1), '' 
    x = bytes(('%s' % c)[:10], 'ascii')
    A = eval(d[x].decode('ascii'))
    while x in d:
        o += '%s: 1€ = %12.10f $\n' % (x.decode('ascii'), A['EUR'])
        c += datetime.timedelta(days=1)
        x = bytes(('%s' % c)[:10], 'ascii')
        if x in d:
            B = eval(d[x].decode('ascii'))
            A = B
    d.close()
    return o
    
def delta2(d, A, B):
    "square distance"
    n, m = __curset__['USD'], __curset__['USD'] 
    for i in [x for x in sorted(__curset__) if x!='USD']:
        n, m = n+A[i]/B[i]*__curset__[i], m+A[i]*A[i]/B[i]/B[i]*__curset__[i]
    return n/m*A['⊔']

def delta1(d, A, B):
    "linear distance"
    A['USD'] = B['USD'] = 1
    d = {B[i]/A[i]*A['⊔']: sum([abs(1-B[i]/B[j]*A[j]/A[i])*__curset__[j] for j in __curset__ if j!=i]) for i in __curset__}
    return min(d, key=d.get)

def application(environ, start_response):
    "wsgi server app"
    mime, o, now, fname, port = 'text/plain; charset=utf8', 'error', '%s' % datetime.datetime.now(), 'default.txt', environ['SERVER_PORT']
    (raw, way) = (environ['wsgi.input'].read(), 'post') if environ['REQUEST_METHOD'].lower() == 'post' else (urllib.parse.unquote(environ['QUERY_STRING']), 'get')
    base, ncok = environ['PATH_INFO'][1:], []
    d = init_dbs(('pub', 'trx', 'blc', 'hid', 'crt', 'igs', 'own', 'obj'), port)
    forex('/%s/%s_%s/rates' % (__app__, __app__, port)) # warning if not updated too frequently
    if   len(raw) ==   5 and way == 'post': o = req_5  (raw)
    elif len(raw) ==   9 and way == 'post': o = req_9  (d, raw)
    #elif len(raw) ==  12 and way == 'post': o = req_12 (d, raw)
    elif len(raw) ==  15 and way == 'post': o = req_15 (d, raw)
    elif len(raw) ==  24 and way == 'post': o = req_24 (d, raw)
    elif len(raw) == 132 and way == 'post': o = req_132(d, raw)
    elif len(raw) == 145 and way == 'post': o = req_145(d, raw)
    #elif len(raw) == 147 and way == 'post': o = req_147(d, raw) # spare removed
    elif len(raw) == 150 and way == 'post': o = req_150(d, raw)
    elif len(raw) == 154 and way == 'post': o = req_154(d, raw)
    elif len(raw) == 156 and way == 'post': o = req_156(d, raw)
    elif len(raw) == 159 and way == 'post': o = req_159(d, raw)
    elif len(raw) == 186 and way == 'post': o = req_186(d, raw)
    elif len(raw) == 300 and way == 'post': o = req_300(d, raw)
    elif way == 'post':
        s = raw.decode('ascii')
        if reg(re.match('cm=(\S{1,12})&alias=(.+)$', s)):
            alias, cm = urllib.parse.unquote(reg.v.group(2).strip()), capture_id(d, reg.v.group(1).strip())
            if cm:
                ok = True
                if 'HTTP_COOKIE' in environ:
                    for x in environ['HTTP_COOKIE'].split(';'):
                        t = x.split('=')
                        if alias == t[0] or cm == t[1]: ok = False
                if ok:
                    xprs = time.time() + 100 * 24 * 3600 # 100 days from now
                    ncok.append(('set-cookie', '%s=%s;expires=%s GMT' % (alias, cm, time.strftime('%a, %d-%b-%Y %T', time.gmtime(xprs)))))
                    if 'HTTP_COOKIE' in environ:
                        environ['HTTP_COOKIE'] += ';%s=%s' % (alias, cm)
                    else:
                        environ['HTTP_COOKIE'] = '%s=%s' % (alias, cm)
                if alias[0] == '@': get_twitter_img(port, alias[1:], cm)
            o, mime = app_index(d, environ), 'text/html; charset=utf-8'
        elif s == 'rem=Effacer+les+cookies':
            for x in environ['HTTP_COOKIE'].split(';'):
                t = x.split('=')
                ncok.append(('set-cookie', '%s=no;expires=Thu, 01 Jan 1970 00:00:00 GMT' % t[0]))            
            del environ['HTTP_COOKIE']
            o, mime = app_index(d, environ), 'text/html; charset=utf-8'
        elif re.match('\S{12}$', s): o = req_9(d, b64tob(bytes(s, 'ascii')))
        elif re.match('@\S{12}$', s): # get Twitter image
            fimg = '/%s/%s_%s/img/%s.png' % (__app__, __app__, port, s[1:])
            if os.path.isfile(fimg): mime, o = 'image/png', open(fimg, 'rb').read()
        elif re.match('\S{16}$', s):  o = req_12 (d, b64tob(bytes(s, 'ascii')))
        elif re.match('\S{20}$', s):  o = req_15 (d, b64tob(bytes(s, 'ascii')))
        elif re.match('\S{32}$', s):  o = req_24 (d, b64tob(bytes(s, 'ascii')))
        elif re.match('\S{176}$', s): o = req_132(d, b64tob(bytes(s, 'ascii')))
        #elif re.match('\S{196}$', s): o = req_147(d, b64tob(bytes(s, 'ascii')))
        elif re.match('\S{200}$', s): o = req_150(d, b64tob(bytes(s, 'ascii')))
        elif re.match('\S{208}$', s): o = req_156(d, b64tob(bytes(s, 'ascii')))
        elif re.match('\S{212}$', s): o = req_159(d, b64tob(bytes(s, 'ascii')))
        elif re.match('\S{248}$', s): o = req_186(d, b64tob(bytes(s, 'ascii')))
        elif re.match('\S{400}$', s): o = req_300(d, b64tob(bytes(s, 'ascii')))
        else: o = "ERROR %s" % (s)
    else: # get
        s = raw # use directory or argument
        if re.match('\S{8}$', base): o = req_8(d, b64tob(bytes(base, 'ascii')))
        elif re.match('ZZ\S{8}$', base): o = req_10(d, b64tob(bytes(base[2:], 'ascii')))
        elif re.match('(\S{2,30})$', base) and len(s) == 196: o = buyig(environ, d, b64tob(bytes(s, 'ascii')), base)
        elif re.match('(\S{2,30})$', base) and len(s) == 36: o, mime = readig(environ, b64tob(bytes(s, 'ascii')), base), 'application/pdf'
        elif re.match('(\S{2,30})$', base) and s == ':': o = '%d:%d:%d' % curpkn('/%s/%s_%s/igf/%s.igf' % (__app__, __app__, port, base))
        elif re.match('(\S{2,30})$', base) and s == '@': o = igregister(environ, d, base)
        elif re.match('\S{12}$', base): o, mime = app_report(d, base, environ), 'text/html; charset=utf-8'
        elif base == '' and s == '': o, mime = app_index(d, environ), 'text/html; charset=utf-8'
        elif s == '': 
            o = 'Attention !\nLe site est temporairement en phase de test de communication avec l\'application iOS8 pour iPhone4S à iPhone6(6+)\nVeuillez nous en excuser\nPour toute question: contact@eurofranc.fr'
        elif base == '' and s == 'users': o, mime = app_users(d, environ), 'text/html; charset=utf-8'
        elif base == '' and s == 'invoice': o, mime = app_invoice(d, environ), 'text/html; charset=utf-8'
        elif base == '' and s == 'invoicePDF': o, mime = app_invoicePDF(d, environ), 'application/pdf'
        elif base == '' and s == '_clean': o = app_clean(d, environ)
        elif base == '' and s == 'transactions': o, mime = app_trx(environ, d), 'text/html; charset=utf-8'
        elif base == '' and s == 'igs': o, mime = app_igs(environ, d), 'text/html; charset=utf-8'
        elif base == '' and s == '_isactive': o = 'ok'
        elif base == '' and s == '_update': o = app_update()
        elif base == '' and s == '_check': o = update_blc(d) + update_ubl(environ, d)
        elif base == '' and s == 'rate1': o = rates('/%s/%s_%s/rates' % (__app__, __app__, port), False)
        elif base == '' and s == 'rate2': o = rates('/%s/%s_%s/rates' % (__app__, __app__, port), True)
        elif base == '' and s == 'rates': o = rates('/%s/%s_%s/rates' % (__app__, __app__, port), True, True)
        elif base == '' and s == 'rates0': o = rates0('/%s/%s_%s/rates' % (__app__, __app__, port))
    start_response('200 OK', [('Content-type', mime)] + ncok)
    return [o if mime in ('application/pdf', 'image/png', 'image/jpg') else o.encode('utf8')] 


def update_cup1(figs, po, ko, p, k):
    "update cup balances after a purchase"
    ig, l = open(figs, 'rb').read(), {}
    s, a = b2i(ig[6:14]), b2i(ig[26:28])
    assert a == 1 # temporary
    i, pu, pi = (len(ig)-28-142*a-s)//167, b2i(ig[14:18]), b2i(ig[18:26])
    assert i > 0
    print (i)
    if i == 1: icm = k*p + (i-k)*(p-1)
    else: icm = k*p + (i-k)*(p-1) - ko*po - (i-1-ko)*(po-1)
    iga = ig[28:37] # if a == 1 !!!!!!
    if icm != 0: l[iga] = icm
    for j in range(1, i):
        rfd, igb = (po if j<=ko else po-1) - (p if j<=k else p-1), ig[142*a+s+167*j-135:142*a+s+167*j-126]
        if rfd != 0: l[igb] = l[igb] + rfd if igb in l else rfd
    prc, igp = p if k==i else p-1, ig[142*a+s+167*i-135:142*a+s+167*i-126]
    if prc != 0: l[igp] = l[igp] - prc if igp in l else -prc
    print (l)

def ubl1(cm):
    figs, bl = '/ef/ef_80/igf/uppr.igf', 0      
    if os.path.isfile(figs):
        ig, rat, sumr = open(figs, 'rb').read(), {}, 0
        s, a = b2i(ig[6:14]), b2i(ig[26:28])
        b, pu, pi = (len(ig)-28-142*a-s)//167, b2i(ig[14:18]), b2i(ig[18:26])
        p, k =  b2i(ig[-8:-4]), b2i(ig[-4:])
        print (a, b, p, k)
        bl = sum([-p if i<k else 1-p for i in filter(lambda j:ig[32+142*a+s+167*j:41+142*a+s+167*j] == cm, range(b))])
    print (bl)

def stat():
    dpub = dbm.open('/ef/ef_80/pub')
    for src in dpub.keys(): print (btob64(src))
    dpub.close()
    dtrx, dblc = dbm.open('/ef/ef_80/trx'), dbm.open('/ef/ef_80/blc')
    for src in dtrx.keys():
        if len(src) == 9:            
            bal, n = int(dblc[src]) if src in dblc else 0, len(dtrx[src])//13
            print ('USER: ', btob64(src), n, bal)
            for x in range(n):
                s = dtrx[src][13*(n-x-1):13*(n-x)]
                (w, ur) = (i2b(0,1), dtrx[s][:9]) if s[4:] == src else (i2b(1,1), s[4:])
                way = '+' if b2i(w) == 1 else '-'
                print (x, datdecode(s[:4]), btob64(ur), way, b2i(dtrx[s][9:11]), b2i(dtrx[s][11:14]), b2i(dtrx[s][14:16]), b2i(dtrx[s][16:18])  )  
    dblc.close()
    dtrx.close()
    print ('crt file')
    dcrt = dbm.open('/ef/ef_80/crt')
    for src in dcrt.keys(): print (btob64(src), b2i(dcrt[src][4:9]))
    dcrt.close()
    print ('igs file')
    digs = dbm.open('/ef/ef_80/igs')
    for i in digs.keys(): print (btob64(i), digs[i])
    digs.close()
    dtrx, digs = dbm.open('/ef/ef_80/trx'), dbm.open('/ef/ef_80/igs')
    for t in filter(lambda x:len(x) == 10, dtrx.keys()):
        n = len(dtrx[t])//10
        for i in range(n):
            s = dtrx[t][10*(n-i-1):10*(n-i)]
            if s in digs and reg(re.match(r'([^/]+)/(\S+)$', digs[s].decode('utf8'))): 
                print('-> %s %s' %(reg.v.group(2), btob64(t[1:])))
    dtrx.close()
    digs.close()
    print ('blc file')
    dblc = dbm.open('/ef/ef_80/blc')
    for i in filter(lambda x:len(x) == 10, dblc.keys()): print (btob64(i[1:]), dblc[i])
    dblc.close()

def set_owner():
    owners = [b'QZs_QO6iFHok',]
    dwn = wopen('/ef/ef_80/own')
    for x in owners: dwn[b64tob(x)] = datencode()
    dwn.close()

if __name__ == '__main__':
    #set_owner()
    base = 'Prototyp'
    toto = b64tob(bytes(base, 'ascii'))
    print (toto)
    #stat()
    #ubl1(b64tob(b'6qfGc2EhJNqW'))
    #update_cup1('/ef/ef_80/igf/uppr.igf', 10, 1, 10, 1)
    #forex('rates3', True)
    #readforex('rates3')
    #testforex()
    #sys.exit()

# End ⊔net!
