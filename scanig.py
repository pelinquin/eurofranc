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

def price(pu, pi, i, ko, po):
    "_"
    x = pu + (i-1)*pu//2
    t = x if x<=pi else pi if pu>2 else pu if i<pu else i if i<pi else pi
    for p in range(t//i-2, t//i+2):
        k = t-i*(p-1)
        if k>0 and k<=i and (p!=po or k<=ko or t==pi or p<=1 or k>=i): return p, k

def generate3():
    ig = open('uppr.pdf', 'rb+').read()
    f, s, pi, li, a, b = open('uppr.igf', 'wb+'), len(ig), 10, 1000, 1, 3
    k, cm = b'AZERTYUIOPQSDF', b64tob(b'ApL7sWemaF7q')
    buyers = [b'QZs_QO6iFHok', b'Il7IijlKWPwK', b'aDFMPHR_f_kO']
    code = btob64(cm + i2b(1, 4) + k) # 9+4+14=27 -> 36
    print (s, 28+142*a+s+167*b)
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
    "add ig-transaction: dat:4+src:9+ref:2+p:4+k:4+sig:132+key:12"  #167 
    po, ko = pi, 1
    for i in range(b):
        po, ko = price(pi, li, i+1, ko, po)
        f.write(i2b(111, 4) + b64tob(buyers[i]) + i2b(i, 2) + i2b(11155555, 132) + i2b(1116655444, 12) + i2b(po, 4) + i2b(ko, 4)) 
    f.close()                             # 28+142*a+s+167*b  
    sys.exit()

def generate0():
    ig = open('uppr.pdf', 'rb+').read()
    f, s, pi, li, a = open('uppr.igf', 'wb+'), len(ig), 10, 1000, 1
    k, cm = b'AZERTYUIOPQSDF', b64tob(b'ubrOTp1p7Yc6')
    code = btob64(cm + i2b(1, 4) + k) # 9+4+14=27 -> 36
    print (s, 28+142*a+s)
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
    f.close()                             
    sys.exit()

def gencheck():
    ""
    f, val, cm, buyer = open('check.igf', 'wb+'), 1000, b64tob(b'ApL7sWemaF7q'), b64tob(b'QZs_QO6iFHok')
    s = 0
    pcup, pefr, dat = 123, 55, 888
    f.write(bytes('⊔', 'utf8')+ i2b(0, 1)) # 4  file-type + algo
    f.write(i2b(dat, 4))                   # 8 date
    f.write(i2b(pcup, 4))                  # 12 ⊔  value
    f.write(i2b(pefr, 4))                  # 15 €f value
    f.write(cm)                            # 24  
    f.write(buyer)                         # 33
    f.write(i2b(6666554444455, 132))       # 165
    # after validation 
    f.close()                              # 165
    sys.exit()

def scan():
    ig, ah, rat = open(sys.argv[1], 'rb').read(), {}, {}
    t, s, m, a = len(ig), b2i(ig[6:14]), b2i(ig[4:6]), b2i(ig[26:28])
    q = 28+142*a+s
    b = (t-q)//167
    p1, pf = b2i(ig[14:18]), b2i(ig[18:26])
    p, k = b2i(ig[-8:-4]) if b>0 else p1, b2i(ig[-4:]) if b>0 else 1
    income = k*p + (b-k)*(p-1) if b>0 else 0
    np, nk = price(p1, pf, b+1, p, k)
    nprc = np if nk == b+1 else np-1
    sumr, tab = 0, []
    print ('%s v%s size:%d/%d nb-authors:%d nb-buyers:%d init-price:%d limit-income:%d income:%d next-price:%d' % (ig[:3].decode('utf8'), b2i(ig[3:4]), t, s, a, b, p1, pf, income, nprc))
    for i in range(a):
        ida = ig[28+10*i:37+10*i]
        ah[ida], rat[ida] = 0, b2i(ig[37+10*i:38+i*142])
        sumr += rat[ida]
    print ('Allocation:', {btob64(x):rat[x] for x in rat})
    for x in rat:
        ah[x] += int(income/rat[x]*sumr) # attention arrondi!
    # check signature
    for i in range(b):
        idb = ig[q+4+167*i:q+13+167*i]
        prc = -p if i<k else 1-p
        ah[idb] = ah[idb] + prc if idb in ah else prc
        #print (' buyer', i+1, ':', btob64(idb), 'key:', btob64(i2b(i, 4) + ig[9+q+167*i:23+q+167*i]))
    assert sum(ah.values()) == 0 
    print ('Balances:', {btob64(x):ah[x] for x in ah})

if __name__ == '__main__':
    if len(sys.argv == 2):
        if sys.argv[1] == 'gen': 
            generate0()
        else:
            scan()
    else:
        gencheck()

