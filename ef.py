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
# POST: (after b64tob)
#    12\S: get user's balance
#  @+12\S: get Twitter profile image 48x48 (png)
#    16\S get transaction at position
#    20\S check transaction (short)
#    32\S check transaction (long)
#   176\S record public-key # temporary !
#   212\S record transaction 
#   400\S record main account pubkey

# TRANSACTION MSG
# date(4)src(9)dst(9)val(2)ref(3):27

# CERTIFICATE MSG
# 

import re, os, sys, urllib.parse, hashlib, http.client, base64, datetime, functools, subprocess, time, smtplib, operator, getpass, dbm.ndbm
import requests, requests_oauthlib
import gmpy2 # for inverse_mod fast computing

__app__    = os.path.basename(__file__)[:-3]
__dfprt__  = 80
__base__   = '/%s/%s_%s/' % (__app__, __app__, __dfprt__)
__ef__     = 'eurofranc'
__email__  = 'contact@%s.fr' % __ef__

_SVGNS     = 'xmlns="http://www.w3.org/2000/svg"'
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
    dtrx, b = ropen(d['trx']), {}
    for t in [x for x in dtrx.keys() if len(x) == 13]:
        src, dst, v = t[4:], dtrx[t][:9], b2i(dtrx[t][9:11])
        b[src], b[dst] = b[src] - v if src in b else (-v), b[dst] + v if dst in b else v
    dtrx.close()
    dblc = wopen(d['blc'])
    for x in b:
        if x in dblc and b[x] != int(dblc[x]): 
            sys.stderr.write('Diff %d %s for %s\n' % (b[x], dblc[x], x))
            dblc[x] = '%d' % b[x]
    dblc.close()

def blc(d, cm):
    "get balance"
    dblc, bal = ropen(d['blc']), 0
    if cm in dblc: 
        bal = int(dblc[cm])
    dblc.close()
    return bal

def debt(d, cm):
    "get max debt"
    dcrt, dbt = ropen(d['crt']), 0
    if cm in dcrt and len(dcrt[cm]) == 141: 
        dat, msg, sig, k, p = dcrt[cm][:4], cm + dcrt[cm][:9], dcrt[cm][-132:], ecdsa(), b64tob(bytes(_ibank_pkey + _ibank_id, 'ascii'))
        k.pt = Point(c521, b2i(p[:66]), b2i(p[66:]))
        if is_future(dat) and k.verify(sig, msg): dbt = b2i(dcrt[cm][4:9])
    dcrt.close()
    return dbt

def is_principal(d, cm):
    ""
    dcrt, res = ropen(d['crt']), False
    if cm in dcrt and len(dcrt[cm]) == 138: 
        dat, msg, sig, k, p = dcrt[cm][:4], cm + dcrt[cm][:6], dcrt[cm][-132:], ecdsa(), b64tob(bytes(_admin_pkey + _admin_id, 'ascii'))
        k.pt = Point(c521, b2i(p[:66]), b2i(p[66:]))
        if is_future(dat) and k.verify(sig, msg): res = True
    dcrt.close()
    return res

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
    return '<a href="./"><img title="Eurofranc 2015, pour l\'économie réelle !" src="%s" width="100"/></a>\n' % (get_image('logo.png'))

def get_image(img):
    "_"
    here = os.path.dirname(os.path.abspath(__file__))
    return 'data:image/png;base64,%s' % base64.b64encode(open('%s/%s' % (here, img), 'rb').read()).decode('ascii')

def getimg(img):
    "_"
    return 'data:image/png;base64,%s' % base64.b64encode(open(img, 'rb').read()).decode('ascii')

def style_html():
    "_"
    o = '<style type="text/css">@import url(http://fonts.googleapis.com/css?family=Schoolbell);h1,h2,p,li,i,b,a,div,input,td,th,footer,svg{font-family:"Lucida Grande", "Lucida Sans Unicode", Helvetica, Arial, Verdana, sans-serif}a.mono,p.mono,td.mono,b.mono{font-family:"Lucida Concole",Courier;font-weight:bold}a.name{margin:50}a{color:DodgerBlue;text-decoration:none}p.alpha{font-family:Schoolbell;color:#F87217;font-size:26pt;position:absolute;top:115;left:80}div.qr,a.qr{position:absolute;top:0;right:0;margin:15}p.note{font-size:9}p.msg{font-size:12;position:absolute;top:0;right:120;color:#F87217}p.stat{font-size:9;position:absolute;top:0;right:20;color:#999}input{font-size:28;margin:3}input.txt{width:200}input.digit{width:120;text-align:right}input.simu{width:120;text-align:right}input[type=checkbox]{width:50}input[type=submit]{color:white;background-color:#AAA;border:none;border-radius:8px;padding:3}p,li{margin:10;font-size:18;color:#333}b.red,td.red{color:red}b.green{color:green}b.blue{color:blue}b.bigorange{font-size:32;color:#F87217}b.biggreen{font-size:32;color:green}td.smallgreen{font-size:9;color:green}b.huge{position:absolute;top:15;left:76;font-size:90;}#wrap{overflow:hidden}a.ppc{font-weight:bold;font-size:.9em}a.ppc:after{font-weight:normal;content:"Cash"}#lcol{float:left;width:360;padding:4}#rcol{margin-left:368;padding:4}footer{bottom:0;color:#444;font-size:10;padding:4}table{margin:1;border:2px solid #999;border-collapse:collapse; background-color:white; opacity:.7}td,th{font-size:11pt;border:1px solid #666;padding:2pt}th{background-color:#DDD}td.num{font-size:12;text-align:right}#c1{float:left;width:23%;padding:1%}#c2{float:left;width:23%;padding:1%}#c3{float:left;width:23%;padding:1%}#c4{float:left;width:23%;padding:1%}h1{color:#888;font-size:25;margin:10 0 0 6}h2{color:#AAA;font-size:18;margin:5 0 0 30}svg{background-color:white}img.book{border:2px outset}text{font-size:18pt}body{margin:0}euro:after{font-size:60%;vertical-align:30%;content:"f"}img{vertical-align:middle}'
    return o + '</style>'

def favicon():
    "_"
    return '<link rel="shortcut icon" type="www/image/png" href="data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAMAAAAoLQ9TAAAABGdBTUEAALGPC/xhBQAAAAFzUkdCAK7OHOkAAAAgY0hSTQAAeiYAAICEAAD6AAAAgOgAAHUwAADqYAAAOpgAABdwnLpRPAAAAXFQTFRF/wCA/wOC/wF//wB5/wB3/wB+/wKB/wqD/0Cg/1+v/z+g/wqF/wWC/wSC/1ms/+Px//////7///v9/2e0/wB0/wR4/wB1/wB8/wCB/wB4/2qz/+32/7fb/7nc//r9/zmb/xiL/4XC/5bL/y6X/wB7/yOP//L4/8fj/xaL/x+P/xKH/9Lp/+Ty/0ul/4LB//3+/ziZ/wmF/7ze/wJ//wB6/6/X//b7//j8//X6/w+I/zOZ/9/v/9rs/0mk/0ym/0um/02m/1ut/222/9Xq/1Kp/weE/wB//wB9/2Gw//D3/+by/ofD/onE/4zG/4fD/wp9/xB//7jZ/wBw/wOB/4/H/c/m/M3l/77f/wuF/7rc/wSD/wBx/3W3/ziV/wBu/wN7/wF6/xOG//3//7Xa/x2N/+v1/9Lo/ySS/yuW/1Co/7rd/1ys//H4/8Lh/8Ph/3y+/3a7/2az/wGB/06m/9zu//z+/wBv/wR7/weB/zmd/1SqcikTHwAAAAFiS0dEEJWyDSwAAAAJcEhZcwAACxMAAAsTAQCanBgAAADvSURBVBjTY2AAAkYmZhYWZlYGGGBjZufg5OTiZuDhZYPw+fgFBIUEhEVExcQlgOolpQQEpGVk5eQVFJWUxRnYVFTVBNQ1JJk1tbQFdHSZGXiZ9QT0DZi5DcUVBIxYjBkYTEwF9PXNhMzNzSz0BfgtWRlYrawFbGzt7B0cnQScXVzdGNw9PAW8vH18/fwDBAKDghkYVEIsBIRCw5zDIzQEIlWAAlHRMQKCsXHxCZKJScnMQAE21pRUgbR0cfeMTPMskADQYdkCAjm5eQL5BYXiRRCnF5cICJYKeJSVS8A8V1FZ5aLMxssI8y7Y+yYQNgBQWiTEKkSv3QAAACV0RVh0ZGF0ZTpjcmVhdGUAMjAxNC0wNS0yNlQxMDozMDoxMCswMjowMP2x9zQAAAAldEVYdGRhdGU6bW9kaWZ5ADIwMTQtMDUtMjZUMTA6MzA6MTArMDI6MDCM7E+IAAAAAElFTkSuQmCC"/>'

def footer():
    "_"
    return '<footer>Contact: <a href="mailto:%s">%s</a><br/><a href="http://cupfoundation.net">⊔FOUNDATION</a> is registered in Toulouse/France SIREN: 399 661 602 00025</footer></html>' % (__email__, __email__)

def app_index(d, env):
    o = header() + favicon() + style_html() + title()
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

def app_users(d):
    o, un = header() + favicon() + style_html() + title() + '<table>', '<euro>&thinsp;€</euro>'
    dpub, dblc = ropen(d['pub']), ropen(d['blc'])
    for i, src in enumerate(dpub.keys()): 
        dbt = debt(d, src)
        typ = '*' if is_principal(d, src) else '' if dbt == 0 else '%d%s' % (dbt, un)
        o += '<tr><td class="num">%d</td><td><a href="./%s" class="mono">%s</a></td><td class="num">%s</td><td class="num">%7.2f%s</td></tr>' % (i+1, btob64(src), btob64(src), typ, int(dblc[src])/100 if src in dblc else 0, un)
    dpub.close()
    dblc.close()
    return o + '</table>' + footer()

def app_trx(d):
    o, un = header() + favicon() + style_html() + title() + '<table>', '<euro>&thinsp;€</euro>'
    dtrx = ropen(d['trx'])
    for i, t in enumerate(dtrx.keys()): 
        if len(t) == 13:            
            prf = btob64(t[4:])[:1] + btob64(dtrx[t][:9])[:1]
            o += '<tr><td class="num">%d</td><td class="num">%s</td><td><a href="./%s" class="mono">%s</a></td><td><a href="%s" class="mono">%s</a></td><td class="mono smallgreen">%s%08d</td><td class="num">%7.2f%s</tr>' % (i+1, datdecode(t[:4]), btob64(t[4:]), btob64(t[4:]), btob64(dtrx[t][:9]), btob64(dtrx[t][:9]), prf ,b2i(dtrx[t][11:14]), b2i(dtrx[t][9:11])/100, un)
    dtrx.close()
    return o + '</table>' + footer()

def app_report(d, src):
    o, un, r = header() + favicon() + style_html() + title(), '<euro>&thinsp;€</euro>', b64tob(bytes(src, 'ascii'))
    dtrx, dblc, dbt = ropen(d['trx']), ropen(d['blc']), debt(d, r)
    typ = '*' if is_principal(d, r) else '' if dbt == 0 else '%d%s' % (dbt, un)
    o += '<table><tr><td class="mono">%s</td><td class="num">%s</td><td class="num">%7.2f%s</td></tr></table><table>' % (src, typ, int(dblc[r])/100 if r in dblc else 0, un) 
    dblc.close()
    if r in dtrx:
        n = len(dtrx[r])//13
        for i in range(n):
            s = dtrx[r][13*(n-i-1):13*(n-i)]
            (w, ur) = (i2b(0,1), dtrx[s][:9]) if s[4:] == r else (i2b(1,1), s[4:])
            dst = btob64(ur)
            prf = dst[:1] + src[:1] if b2i(w) == 1 else src[:1] + dst[:1]
            way = '+' if b2i(w) == 1 else '-'
            o += '<tr><td class="num">%d</td><td class="num">%s</td><td><a href="./%s" class="mono">%s</a></td><td class="mono smallgreen">%s%08d</td><td class="num">%s%7.2f%s</td></tr>' % (i+1, datdecode(s[:4]), btob64(ur), btob64(ur), prf, b2i(dtrx[s][11:14]), way, b2i(dtrx[s][9:11])/100, un)
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

def application(environ, start_response):
    "wsgi server app"
    mime, o, now, fname, port = 'text/plain; charset=utf8', 'error', '%s' % datetime.datetime.now(), 'default.txt', environ['SERVER_PORT']
    (raw, way) = (environ['wsgi.input'].read(), 'post') if environ['REQUEST_METHOD'].lower() == 'post' else (urllib.parse.unquote(environ['QUERY_STRING']), 'get')
    base, ncok = environ['PATH_INFO'][1:], []
    d = init_dbs(('pub', 'trx', 'blc', 'hid', 'crt'), port)
    if way == 'post':
        s = raw.decode('ascii')
        if reg(re.match('cm=(\S{1,12})&alias=(.+)$', s)):
            alias, cm = urllib.parse.unquote(reg.v.group(2)), capture_id(d, reg.v.group(1))
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
        elif re.match('\S{12}$', s): # get balance | src:9 len(9->12)
            r = b64tob(bytes(s, 'ascii'))
            dpub = ropen(d['pub'])
            if r in dpub: 
                o = '%d' % blc(d, r)
            dpub.close()
        elif re.match('@\S{12}$', s): # get Twitter image
            fimg = '/%s/%s_%s/img/%s.png' % (__app__, __app__, port, s[1:])
            if os.path.isfile(fimg): mime, o = 'image/png', open(fimg, 'rb').read()
        elif re.match('\S{16}$', s): # get transaction | src:9+pos:3 len(12->16)
            r = b64tob(bytes(s, 'ascii'))
            src, pos, dtrx = r[:9], b2i(r[9:]), ropen(d['trx'])
            if src in dtrx:
                n = len(dtrx[src])//13
                if pos >= 0 and pos < n:
                    sl = dtrx[src][13*pos:13*(pos+1)]
                    (w, ur) = (i2b(0,1), dtrx[sl][:9]) if sl[4:] == src else (i2b(1,1), sl[4:])
                    o = btob64(sl[:4] + ur + dtrx[sl][9:14] + w + i2b(n, 2)) 
                    # return | dat:4+usr:9+val:2+ref:3+way:1+max:2 len(21->28)
                    # QRCODE:15 btob64(dat+usr:12+val)
            dtrx.close()
        elif re.match('\S{20}$', s): # check transaction (short) | dat:4+scr:9+val:2 len(15->20)
            r = b64tob(bytes(s, 'ascii'))
            u, dat, src, val, dtrx = r[:13], r[:4], r[4:13], r[:-2], ropen(d['trx'])
            if u in dtrx and dtrx[u][9:11] == val: 
                o = '%d:%d' % (b2i(dtrx[u][14:16]), b2i(dtrx[u][16,18]))
            dtrx.close()
        elif re.match('\S{32}$', s): # check transaction (long) | dat:4+scr:9+dst:9+val:2 len(24->32)
            r = b64tob(bytes(s, 'ascii'))
            u, dst, val, dtrx = r[:13], r[13:22], r[:-2], ropen(d['trx'])
            if u in dtrx and dtrx[u][:9] == dst and dtrx[u][9:11] == val: 
                o = '%d:%d' % (b2i(dtrx[u][14:16]), b2i(dtrx[u][14:16]))
            dtrx.close()
        elif re.match('\S{176}$', s): # register publickey | pbk:132 len(132->176) SPAMING RISK -> SHALL BE REMOVED !
            r = b64tob(bytes(s, 'ascii'))
            pub, src, v, dpub = r, r[-9:], r[:-9], wopen(d['pub'])
            if src in dpub: o = 'old'
            else: dpub[src], o = v, 'new'
            dpub.close()
        elif re.match('\S{196}$', s): # admin certificate: usr:9+dat:4+spr:2+sig:132 len(147)->196 
            r = b64tob(bytes(s, 'ascii'))
            src, v, dat, msg, sig, k, p = r[:9], r[9:], r[9:13], r[:15], r[-132:], ecdsa(), b64tob(bytes(_admin_pkey + _admin_id, 'ascii'))
            k.pt = Point(c521, b2i(p[:66]), b2i(p[66:]))
            if is_future(dat) and k.verify(sig, msg): 
                o, dcrt = 'ok', wopen(d['crt'])
                dcrt[src] = v 
                dcrt.close()
        elif re.match('\S{200}$', s): # ibank certificate: bnk:9+dat:4+dbt:5+sig:132 len(150)->200 
            r = b64tob(bytes(s, 'ascii'))
            src, v, dat, dbt, msg, sig, k, p = r[:9], r[9:], r[9:13], b2i(r[13:18]), r[:18], r[-132:], ecdsa(), b64tob(bytes(_ibank_pkey + _ibank_id, 'ascii'))
            k.pt = Point(c521, b2i(p[:66]), b2i(p[66:]))
            if is_future(dat) and k.verify(sig, msg): 
                o, dcrt = 'ok', wopen(d['crt'])
                dcrt[src] = v 
                dcrt.close()
        elif re.match('\S{212}$', s): # add transaction msg:27+sig:132 len(159->212)
            r = b64tob(bytes(s, 'ascii'))
            u, dat, v, src, dst, val, ref, msg, sig, k, dpub = r[:13], r[:4], r[13:-132], r[4:13], r[13:22], b2i(r[22:24]), b2i(r[24:27]), r[:-132], r[-132:], ecdsa(), ropen(d['pub'])
            if src in dpub and dst in dpub and src != dst:
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
        elif re.match('\S{400}$', s): # register main account: dat:4+hashid:32+pubkey:132+sig:132 len(300->400)
            r = b64tob(bytes(s, 'ascii'))
            dat, hid, src, pk1, pk2, v, msg, sig, k = r[:4], r[4:36], r[159:168], r[36:102], r[102:168], r[36:159], r[:-132], r[-132:], ecdsa()
            k.pt = Point(c521, b2i(pk1), b2i(pk2))
            if k.verify(sig, msg):
                dpub, dhid = wopen(d['pub']), wopen(d['hid'])
                if hid not in dhid:
                    o, dhid[src], dhid[hid] = 'ok', dat + hid + sig, src
                if src not in dpub: dpub[src] = v
                dhid.close()
                dpub.close()
        else: o = "%s" % s
    else: # get
        s = raw # use directory or argument
        if re.match('\S{12}$', base): o, mime = app_report(d, base), 'text/html; charset=utf-8'
        elif base == '' and s == '': o, mime = app_index(d, environ), 'text/html; charset=utf-8'
        elif s == '': 
            o = 'Attention !\nLe site est temporairement en phase de test de communication avec l\'application iOS8 pour iPhone4S à iPhone6(6+)\nVeuillez nous en excuser\nPour toute question: contact@eurofranc.fr'
            update_blc(d)
        elif base == '' and s == 'users': o, mime = app_users(d), 'text/html; charset=utf-8'
        elif base == '' and s == 'transactions': o, mime = app_trx(d), 'text/html; charset=utf-8'
        elif base == '' and s == '_isactive': o = 'ok'
        elif base == '' and s == '_update': o = app_update()
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
    dcrt = dbm.open('/ef/ef_80/crt')
    for src in dcrt.keys(): print (btob64(src), b2i(dcrt[src][4:9]))

# End ⊔net!
