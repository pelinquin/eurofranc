#!/usr/bin/python3
# -*- coding: utf-8 -*-
# Welcome to ⊔net!

import sys, re, base64

PAD = lambda s:(len(s)%2)*'0'+s[2:]

def i2b(x, n=1):
    "int to bytes with n padding"
    z = bytes.fromhex(PAD(hex(x)))
    return ((n-len(z))%n)*bytes.fromhex('00') + z

def b2i(x):
    "bytes to int"
    return int.from_bytes(x, 'big')

def btob64(c):
    "bytes to base64"
    return base64.urlsafe_b64encode(c).decode('ascii').strip('=')

def b64tob(c):
    "base64 to bytes"
    return base64.urlsafe_b64decode(c + b'='*((4-(len(c)%4))%4))

def price_max(p1, pf, i):
    if p1*i < pf: return p1, i
    for j in range(p1):
        k = pf-(p1-j-1)*i
        if k>0: return p1-j, k

def price(p1, pf, i):
    return price_max(p1, pf, i)

def generate():
    ig = open('uppr.pdf', 'rb+').read()
    f, s, pi, li, a, b = open('uppr.igf', 'wb+'), len(ig), 10, 1000, 1, 3
    k, cm = b'AZERTYUIOPQSDF', b64tob(b'ApL7sWemaF7q')
    buyers = [b'QZs_QO6iFHok', b'Il7IijlKWPwK', b'aDFMPHR_f_kO']
    code = btob64(cm + i2b(1, 4) + k) # 9+4+14=27 -> 36
    print (s, 28+142*a+s+159*b)
    print ('cup/uppr:%s' % code)
    f.write(bytes('⊔', 'utf8')+ i2b(1,1)) # 4  file-type + algo
    f.write(i2b(1,  2))                   # 6  ig type
    f.write(i2b(s,  8))                   # 14 ig size 
    f.write(i2b(pi, 4))                   # 18 price-init
    f.write(i2b(li, 8))                   # 26 limit-income
    f.write(i2b(a,  2))                   # 28 number authors 
    for i in range(a): f.write(cm + i2b(100, 1)) 
    f.write(ig)                           # 28+10*a+s 
    for i in range(a): f.write(i2b(6666554444455, 132)) # 28+142*a+s 
    "add ig-transaction: dat:4+src:9+ref:2+sig:132+k:12"
    for i in range(b): f.write(i2b(111, 4) + b64tob(buyers[i]) + i2b(1,2) + i2b(11155555, 132) + i2b(1116655444, 12)) 
    f.close()                             # 28+142*a+s+159*b 
    sys.exit()

if __name__ == '__main__':
    if sys.argv[1] == 'gen': generate()
    ig, ah, rat = open(sys.argv[1], 'rb').read(), {}, {}
    t, s, m, a = len(ig), b2i(ig[6:14]), b2i(ig[4:6]), b2i(ig[26:28])
    q = 28+142*a+s
    b = (t-q)//159
    p1, pf = b2i(ig[14:18]), b2i(ig[18:26])
    p, k = price(p1, pf, b)
    income = k*p + (b-k)*(p-1)
    np, nk = price(p1, pf, b+1)
    sumr, tab = 0, []
    print ('%s v%s size:%d/%d nb-authors:%d nb-buyers:%d init-price:%d limit-income:%d current-price:%d' % (ig[:3].decode('utf8'), b2i(ig[3:4]), t, s, a, b, p1, pf, np))
    for i in range(a):
        ida = ig[28+10*i:37+10*i]
        ah[ida], rat[ida] = 0, b2i(ig[37+10*i:38+i*142])
        sumr += rat[ida]
    print ('Allocation:', {btob64(x):rat[x] for x in rat})
    for x in rat:
        ah[x] += int(income/rat[x]*sumr) # attention arrondi!
    # check signature
    for i in range(b):
        idb = ig[q+4+159*i:q+13+159*i]
        prc = -p if i<=k else 1-p
        ah[idb] = ah[ihb] + prc if idb in ah else prc
        #print (' buyer', i+1, ':', btob64(idb), 'key:', btob64(i2b(i, 4) + ig[9+q+159*i:23+q+159*i]))
    assert sum(ah.values()) == 0 
    print ('Balances:', {btob64(x):ah[x] for x in ah})



