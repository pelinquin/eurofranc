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

if __name__ == '__main__':
    ig, ah = open(sys.argv[1], 'rb').read(), {}
    t, s, a = len(ig), b2i(ig[11:15]), b2i(ig[15:16])
    p = 16+142*a+s
    b = (t-p)//23
    print (ig[:3].decode('utf8'), ' igf size:', t, 'version:', b2i(ig[3:4]))
    print ('init-price:', b2i(ig[4:7]), 'limit-income:', b2i(ig[7:11]), 'ig-size:', s)
    print ('nb-authors:', a, 'nb-buyers:', b)
    for i in range(a):
        ida = ig[16+i*142:25+i*142]
        ah[ida] = 0
        print ('seller', i+1, ':', btob64(ida), 'ratio:', b2i(ig[25+i*142:26+i*142]))
        sig = ig[26+i*142:158+i*142]
    for i in range(b):
        idb = ig[p+i*23:9+p+i*23]
        ah[idb] = 0
        print (' buyer', i+1, ':', btob64(idb), 'key:', btob64(i2b(i, 4) + ig[9+p+i*23:23+p+i*23]))
    np = 10
    print ('balance:', ah)
    print ('next price:', np)
