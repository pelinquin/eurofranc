#!/usr/bin/python3
# -*- coding: utf-8 -*-
# Welcome to ⊔net!
#-----------------------------------------------------------------------------
#  © Copyright 2014 ⊔Foundation
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
#    * The PyCrypt library is far too complex for our needs so we used a code 
#      for AES inspired from:
#      Josh Davis ( http://www.josh-davis.org )
#      Laurent Haan (http://www.progressive-coding.com)
#    * QRcode is extented to PDF and SVG from the inspired code of:
#      Sam Curren (porting from Javascript)
#    * Encryption with ECC use an idea of jackjack-jj on github
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

# API reminder
# GET: 
#    NULL: index page + cookie management
#    12\S: HTML balance report
#    20\S: transaction page
# POST: 
# b13->@+12\S: get Twitter profile image 48x48 (png)
# b9->12\S: get user's balance
# b12->16\S get transaction at position
# b15->20\S check transaction (short)
# b24->32\S check transaction (long)
# b132->176\S record public-key # temporary !
# b147->196\S Admin certificate
# b150->200\S Ibank certificate
# b156->208\S user principal certificat (short) temporary !
# b159->212\S record transaction 
# b186->248\S user principal certificate (long)
# b300->400\S record main account pubkey 

import re, os, sys, urllib.parse, hashlib, http.client, base64, datetime, functools, subprocess, time, smtplib, operator, getpass, dbm.ndbm
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
    "_"
    dtrx, b , o, k = ropen(d['trx']), {}, 'ok', ecdsa()
    for t in [x for x in dtrx.keys() if len(x) == 13]:
        src, dst, v, msg, sig, dpub = t[4:], dtrx[t][:9], b2i(dtrx[t][9:11]), t + dtrx[t][:14], dtrx[t][-132:], ropen(d['pub'])
        k.pt = Point(c521, b2i(dpub[src][:66]), b2i(dpub[src][66:]))
        dpub.close()
        if k.verify(sig, msg): # takes long time ! 
            b[src], b[dst] = b[src] - v if src in b else (-v), b[dst] + v if dst in b else v
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
    "_"
    dtrx, b, o = ropen(d['trx']), {}, 'ok'
    for t in filter(lambda x:len(x) == 10, dtrx.keys()):
        n, b[t] = len(dtrx[t])//10, 0
        for i in range(n):
            s = dtrx[t][10*(n-i-1):10*(n-i)]
            digs = ropen(d['igs'])
            if s in digs and reg(re.match(r'([^/]+)/(\S+)$', digs[s].decode('utf8'))): 
                b[t] += ubl(env, reg.v.group(2), t[1:])
            digs.close()
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

def update_ubl_url(env, d, url):
    "list all cm involved in url end update dblc for each cm" 
    figs, ll = '/%s/%s_%s/igf/%s.igf' % (__app__, __app__, env['SERVER_PORT'], url), {}  
    if os.path.isfile(figs):
        ig, rat, sumr = open(figs, 'rb').read(), {}, 0
        s, a = b2i(ig[6:14]), b2i(ig[26:28])
        b = (len(ig)-28-142*a-s)//159
        if b>0:
            p, k  = cupprice(b2i(ig[14:18]), b2i(ig[18:26]), b)
            ll = {ig[28+10*i:37+10*i]:True for i in range(a) }
            ll.update({ig[32+142*a+s+159*j:41+142*a+s+159*j]:True for j in range(b)})
    dblc = ropen(d['blc'])
    for cm in ll: dblc[b'@' + cm] = ubl(env, url, cm)
    dblc.close()
    return ll

def nbt(d, cm):
    "get total transaction nb"
    dtrx, n = ropen(d['trx']), 0
    if cm in dtrx: 
        n = len(dtrx[cm])//13
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
        b = (len(ig)-28-142*a-s)//159
        if b == 0: return 0
        p, k  = cupprice(b2i(ig[14:18]), b2i(ig[18:26]), b)
        for i in range(a):
            ida = ig[28+10*i:37+10*i]
            rat[ida] = b2i(ig[37+10*i:38+10*i])
            sumr += rat[ida]
        bl = sum([int(k*p+(b-k)*(p-1)/rat[x]*sumr) for x in filter(lambda y:y == cm, rat)]) + sum([-p if i<k else 1-p for i in filter(lambda j:ig[32+142*a+s+159*j:41+142*a+s+159*j] == cm, range(b))])
    return bl

def posubl(env, url, cm):
    "cup positions"
    figs = '/%s/%s_%s/igf/%s.igf' % (__app__, __app__, env['SERVER_PORT'], url)   
    if os.path.isfile(figs):
        ig = open(figs, 'rb').read()
        s, a = b2i(ig[6:14]), b2i(ig[26:28])
        b = (len(ig)-28-142*a-s)//159
        for i in range(a):
            if ig[28+10*i:37+10*i] == cm: return '%dx' % b
        for i in range(b):
            oft = 142*a+s+159*i
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
        for i in range((len(ig)-28-142*a-s)//159):
            ofst = 142*a+s+159*i
            if cm == ig[32+ofst:41+ofst]: return '%s_%05d' % (btob64(cm)[:1], b2i(ig[41+ofst:43+ofst]))

def curblc(fig):
    "current cup price"
    p = 0
    if os.path.isfile(fig): 
        ig = open(fig, 'rb').read()
        s, a = b2i(ig[6:14]), b2i(ig[26:28])
        p, k  = cupprice(b2i(ig[14:18]), b2i(ig[18:26]), 1+(len(ig)-28-142*a-s)//159)
    return p    

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
    o = '<style type="text/css">@import url(http://fonts.googleapis.com/css?family=Schoolbell);h1,h2,p,li,i,b,a,div,input,td,th,footer,svg{font-family:"Lucida Grande", "Lucida Sans Unicode", Helvetica, Arial, Verdana, sans-serif}a.mono,p.mono,td.mono,b.mono{font-family:"Lucida Concole",Courier;font-weight:bold}a.name{margin:50}a{color:DodgerBlue;text-decoration:none}p.alpha{font-family:Schoolbell;color:#F87217;font-size:26pt;position:absolute;top:115;left:80}div.qr,a.qr{position:absolute;top:0;right:0;margin:15}p.note{font-size:9}p.msg{font-size:12;position:absolute;top:0;right:120;color:#F87217}p.stat{font-size:9;position:absolute;top:0;right:20;color:#999}input{font-size:28;margin:3}input.txt{width:210}input.digit{width:120;text-align:right}input.simu{width:120;text-align:right}input[type=checkbox]{width:50}input[type=submit]{color:white;background-color:#AAA;border:none;border-radius:8px;padding:3}p,li{margin:10;font-size:18;color:#333}b.red,td.red{color:red}b.green{color:green}b.blue{color:blue}b.bigorange{font-size:32;color:#F87217}b.biggreen{font-size:32;color:green}td.smallgreen{font-size:9;color:green}b.huge{position:absolute;top:15;left:76;font-size:90;}#wrap{overflow:hidden}a.ppc{font-weight:bold;font-size:.9em}a.ppc:after{font-weight:normal;content:"Cash"}#lcol{float:left;width:360;padding:4}#rcol{margin-left:368;padding:4}footer{bottom:0;color:#444;font-size:10;padding:4}table{margin:1;border:2px solid #999;border-collapse:collapse; background-color:white; opacity:.7}td,th{font-size:11pt;border:1px solid #666;padding:2pt}th{background-color:#DDD}td.num{font-size:12;text-align:right}#c1{float:left;width:23%;padding:1%}#c2{float:left;width:23%;padding:1%}#c3{float:left;width:23%;padding:1%}#c4{float:left;width:23%;padding:1%}h1{color:#888;font-size:25;margin:10 0 0 6}h2{color:#AAA;font-size:18;margin:5 0 0 30}svg{background-color:white}img.book{border:2px outset}text{font-size:18pt}body{margin:0}euro:after{font-size:60%;vertical-align:30%;content:"f"}img{vertical-align:middle}'
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
    o += '<table><tr><td>%s</td><td class="num">%d users</td><td><a href="./?transactions" class="num">transactions</a></td></tr></table><table>' % (title(), len(dpub.keys())) 
    for i, src in enumerate(dpub.keys()): 
        fc = '/%s/%s_%s/img/%s.png' % (__app__, __app__, env['SERVER_PORT'], btob64(src))
        img = getimg(fc) if os.path.isfile(fc) else get_image('user48.png')
        bl = blc(d, src, True)
        #bl = tublc(env, d, src)
        o += '<tr><td class="num">%d</td><td><img width="24" src="%s"/></td><td><a href="./%s" class="mono">%s</a></td><td class="num">%s</td><td class="num">%04d</td><td class="num">%7.2f%s</td><td class="num">%7d&thinsp;⊔</td></tr>' % (i+1, img, btob64(src), btob64(src), get_type(d, src), nbt(d, src), int(dblc[src])/100 if src in dblc else 0, un, bl)
    dpub.close()
    dblc.close()
    return o + '</table>' + footer()

def app_trx(env, d):
    o, un, uc = header() + favicon() + style_html(), '<euro>&thinsp;€</euro>', '&thinsp;⊔'
    dtrx = ropen(d['trx'])
    tab = [z for z in filter(lambda x:len(x) == 13, dtrx.keys())]
    o += '<table><tr><td>%s</td><td><a href="./?users" class="num">users</a></td><td class="num">%d transactions</td></tr></table><table>' % (title(), len(tab)) 
    for i, t in enumerate(filter(lambda x:len(x) == 13, dtrx.keys())):
        if len(dtrx[t]) == 150: 
            prf = btob64(t[4:])[:1] + btob64(dtrx[t][:9])[:1]
            o += '<tr><td class="num">%d</td><td class="num">%s</td><td><a href="./%s" class="mono">%s</a></td><td><a href="%s" class="mono">%s</a></td><td class="mono smallgreen">%s%07d</td><td class="num">%7.2f%s</td></tr>' % (i+1, datdecode(t[:4]), btob64(t[4:]), btob64(t[4:]), btob64(dtrx[t][:9]), btob64(dtrx[t][:9]), prf, b2i(dtrx[t][11:14]), b2i(dtrx[t][9:11])/100, un)
    j = 0
    for t in filter(lambda x:len(x) == 10, dtrx.keys()):
        n = len(dtrx[t])//10
        for i in range(n):
            s = dtrx[t][10*(n-i-1):10*(n-i)]
            digs = ropen(d['igs'])
            if s in digs:
                url = digs[s].decode('utf8')
                if reg(re.match(r'([^/]+)(/\S+)$', url)):
                    dat, ref = posubl(env, reg.v.group(2), t[1:]), refubl(env, reg.v.group(2), t[1:])
                    o += '<tr><td class="num">%d</td><td class="num">%s</td><td><a href="./%s" class="mono">%s</a></td><td><a href="%s" class="num">%s</a></td><td class="mono smallgreen">%s</td><td class="num">%7d&thinsp;⊔</td></tr>' % (j+1, dat, btob64(t[1:]), btob64(t[1:]), url, url, ref, ubl(env, reg.v.group(2), t[1:]))
                    j += 1
            digs.close()
    dtrx.close()
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
                way = '+' if b2i(w) == 1 else '-'
                fc = '/%s/%s_%s/img/%s.png' % (__app__, __app__, env['SERVER_PORT'], dst)
                img = getimg(fc) if os.path.isfile(fc) else get_image('user48.png')
                o += '<tr><td class="num">%03d</td><td class="num">%s</td><td><a href="./%s" class="mono"><img width="24" src="%s"/> %s</a></td><td class="mono smallgreen">%s%07d</td><td class="num">%s%7.2f%s</td></tr>' % (n-i, datdecode(s[:4]), btob64(ur), img, btob64(ur), prf, b2i(dtrx[s][11:14]), way, b2i(dtrx[s][9:11])/100, un)
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

##### ⊔ management
def price_max(p1, pf, i):
    if p1*i < pf: return p1, i
    for j in range(p1):
        k = pf-(p1-j-1)*i
        if k>0: return p1-j, k

def price_min(p1, pf, i):
    if i >= pf: return 1, pf
    if i >= p1: return 1, i
    p = 1+(p1-1)//i
    for k in range (1, i+1):
        if k*p +(i-k)*(p-1) == p1: return p, k

def price_xi(pu, pi, j, xi=2):
    ko, po = 1, pu
    for i in range(1, j+1):
        x = pu + (i-1)*pu//xi
        t = x if x<=pi else pi if xi<pu else pu if i<pu else i if i<pi else pi
        for p in range(t//i-2, t//i+2):
            k = t-i*(p-1)
            if k>0 and k<=i and (p!=po or k<=ko or t==pi or p<=1 or k>=i): 
                po, ko = p, k
                break
    return p, k

def cupprice(p1, pf, i):
    return price_xi(p1, pf, i)

#####

def req_5(r):
    "is active"
    return 'ok' if r == b'ef0.1' else ''

def req_9(d, r):
    "get balance €f + nb transactions + balance cup + nb igs | src:9"
    o = '%d:%d:%d:%d' % (blc(d, r), nbt(d, r), blc(d, r, True), nbig(d, r))
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
    "user principal certificate (short): usr:9+dat:4+adm:9:spr:2+sig:132"
    usr, v, dat, adm, msg, sig, k, o = r[:9], r[9:], r[9:13], r[13:22], r[:24], r[-132:], ecdsa(), 'error'
    if is_mairie(d, adm):
        dhid = ropen(d['hid'])
        if adm in dhid: h = dhid[adm][4:36] # next !
        dhid.close()
        dpub = ropen(d['pub'])
        k.pt = Point(c521, b2i(dpub[adm][:66]), b2i(dpub[adm][66:]+adm))
        dpub.close()
        if is_future(dat) and k.verify(sig, msg): o = set_crt(d, usr, v) 
    return o

def req_159(d, r): 
    "add transaction: dat:4+src:9+dst:9+val:2+ref:3+sig:132"
    u, dat, v, src, dst, val, ref, msg, sig, k, dpub, o = r[:13], r[:4], r[13:-132], r[4:13], r[13:22], b2i(r[22:24]), b2i(r[24:27]), r[:-132], r[-132:], ecdsa(), ropen(d['pub']), 'error'
    if src in dpub and dst in dpub and src != dst and val > 0:
        k.pt = Point(c521, b2i(dpub[src][:66]), b2i(dpub[src][66:]+src))
        dpub.close()
        if k.verify(sig, msg): 
            dtrx = wopen(d['trx'])
            if u in dtrx: o = '%d:%d' % (b2i(dtrx[u][14:16]), b2i(dtrx[u][16:18]))
            else:
                if blc(d, src) + debt(d, src)*100 >= val:
                    dtrx[src] = dtrx[src] + u if src in dtrx else u # shortcut
                    dtrx[dst] = dtrx[dst] + u if dst in dtrx else u # shortcut
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

def buy_ig(env, d, r, base):
    "_"
    figf, url, o = '/%s/%s_%s/igf/%s.igf' % (__app__, __app__, env['SERVER_PORT'], base), '%s/%s' % (env['SERVER_NAME'], base), 'error'
    src, tg, igh, msg, sig, k, vu = r[4:13], b'@' + r[4:13], hashlib.sha1(url.encode('utf8')).digest()[:10], r[:-132], r[-132:], ecdsa(), False
    if os.path.isfile(figf):
        ig = open(figf, 'rb').read()
        s, a = b2i(ig[6:14]), b2i(ig[26:28])
        b = (len(ig)-28-142*a-s)//159
        dpub = wopen(d['pub'])                    
        k.pt = Point(c521, b2i(dpub[src][:66]), b2i(dpub[src][66:]+src))
        dpub.close()
        for i in range(b):
            ce = ig[28+142*a+s+159*i:28+142*a+s+159*(i+1)] 
            if ce[:147] == r:
                o, vu = btob64(ce[4:13] + i2b(i, 6) + ce[-12:]), True
        if not vu and blc(d, src, True) + debt(d, src) + 100 > curblc(figf):
            if k.verify(sig, msg + base.encode('utf8')):
                dtrx = wopen(d['trx'])
                if tg in dtrx:
                    if igh not in {dtrx[tg][i:i+10]:True for i in range(0, len(dtrx[tg]), 10)}:
                        dtrx[tg] += igh 
                else:
                    dtrx[tg] = igh
                dtrx.close()
                update_ubl_url(env, d, url)
                sk = hashlib.sha1(os.urandom(32)).digest()[:12]
                open(figf, 'ab').write(r + sk)
                o = btob64(src + i2b(b+1, 6) + sk)
            else:
                o += ' signature'
        else:
            o += ' again'
    return o

def read_ig(env, rk, base):
    "_"
    figf, o = '/%s/%s_%s/igf/%s.igf' % (__app__, __app__, env['SERVER_PORT'], base), ''
    p, u1, k1 = b2i(rk[9:15]), rk[:9], rk[15:]
    if os.path.isfile(figf): 
        r = open(figf, 'rb').read()
        s, a, t = b2i(r[6:14]), b2i(r[26:28]), len(r)
        b = (t-28-142*a-s)//159
        if p <= b:
            ce = r[28+142*a+s+159*(p-1):28+142*a+s+159*(p)]
            if ce[4:13] == u1 and ce[-12:] == k1: o = r[28+10*a:s+28+10*a]
    return o

def application(environ, start_response):
    "wsgi server app"
    mime, o, now, fname, port = 'text/plain; charset=utf8', 'error', '%s' % datetime.datetime.now(), 'default.txt', environ['SERVER_PORT']
    (raw, way) = (environ['wsgi.input'].read(), 'post') if environ['REQUEST_METHOD'].lower() == 'post' else (urllib.parse.unquote(environ['QUERY_STRING']), 'get')
    base, ncok = environ['PATH_INFO'][1:], []
    d = init_dbs(('pub', 'trx', 'blc', 'hid', 'crt', 'igs'), port)
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
    #elif len(raw) == 156 and way == 'post': o = req_156(d, raw) # spare removed
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
        #elif re.match('\S{208}$', s): o = req_156(d, b64tob(bytes(s, 'ascii')))
        elif re.match('\S{212}$', s): o = req_159(d, b64tob(bytes(s, 'ascii')))
        elif re.match('\S{248}$', s): o = req_186(d, b64tob(bytes(s, 'ascii')))
        elif re.match('\S{400}$', s): o = req_300(d, b64tob(bytes(s, 'ascii')))
        else: o = "ERROR %s" % (s)
    else: # get
        s = raw # use directory or argument
        if re.match('(\S{2,30})$', base) and len(s) == 196: 
            o = buy_ig(environ, d, b64tob(bytes(s, 'ascii')), base)
        elif re.match('(\S{2,30})$', base) and len(s) == 36: 
            o = read_ig(env, b64tob(bytes(s, 'ascii')), base)
            if o != '': mime = 'application/pdf'
        elif re.match('(\S{2,30}):$', base) and s == '': # current price
            o = '%d' % curblc('/%s/%s_%s/igf/%s.igf' % (__app__, __app__, port, base[:-1]))
        elif re.match('(\S{2,30})$', base) and s == '@': o = igregister(environ, d, base)
        elif re.match('\S{12}$', base): o, mime = app_report(d, base, environ), 'text/html; charset=utf-8'
        elif base == '' and s == '': o, mime = app_index(d, environ), 'text/html; charset=utf-8'
        elif s == '': 
            o = 'Attention !\nLe site est temporairement en phase de test de communication avec l\'application iOS8 pour iPhone4S à iPhone6(6+)\nVeuillez nous en excuser\nPour toute question: contact@eurofranc.fr'
        elif base == '' and s == 'users': o, mime = app_users(d, environ), 'text/html; charset=utf-8'
        elif base == '' and s == 'transactions': o, mime = app_trx(environ, d), 'text/html; charset=utf-8'
        elif base == '' and s == '_isactive': o = 'ok'
        elif base == '' and s == '_update': o = app_update()
        elif base == '' and s == '_check': o = update_blc(d) + update_ubl(environ, d)
    start_response('200 OK', [('Content-type', mime)] + ncok)
    return [o if mime in ('application/pdf', 'image/png', 'image/jpg') else o.encode('utf8')] 

if __name__ == '__main__':
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


# End ⊔net!
