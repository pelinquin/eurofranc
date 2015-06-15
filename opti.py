#!/usr/bin/python3
# v0.1 -> coq-club request - 2015, June

# The following is a possible discrete solution to Pelinquin's equation: 
#   $\mathcal{T}_i^{\nearrow{}}\!=\,{i}\mathcal{P}_i^{\searrow{}}$
# The rule: "Each buyer had paid the same amount at any time" (on continious world)
#   is translated in descrete world by:
# "The maximum difference of prices between buyers shall be one"
# So the buyers set is decomposed of two subsets; the first had pay 'p', the second had pay 'p-1'
#   and we have at any time t = kp+(i-k)(p-1) at the #i buyer.
# The challenge on discret (integers) world is to ensure with the most optimized algorithm that:
#   1/ the cumulated income t is always increasing
#   2/ a buyer is only asked to pay once, and get refunded (up to the price minus 1) after 
# Note that it may probably exist other smarter algorithms !
# QUESTION A/ I did not succeed in removing the previous values of p and k in the 'value' iterative function computation
# QUESTION B/ I'm looking for the proof that POST(1,2) conditions are always true.  
# QUESTION C/ I do not have the proof that if 'v_max === value(x=100)' and 'v_min === value(x=0)'
#
# Any suggestion/help please contact: 
#   laurent.fournier@cupfoundation.net
#   laurent.fournier@pluggle.fr
#
# Last Paper: http://arxiv.org/pdf/1405.2051.pdf

def value(d, f, i, p, k, x):
    assert d>0 and f>=d and x>=0 and x<=100 and i>0 and p>=0 and k>=0 and k<=i #PRECOND
    if i == 1: return d, 1
    if i >= f: return 1, f # C
    r, s, w = p if k==i-1 else p-1, 1 if p==1 else 0, k+(i-1)*(p-1)
    u, v = w+s, w+r if w+r<f else f
    t = ((100-x)*u+x*v)//100
    q = (t-1)//i
    return 1+q, t-i*q # A,B

def v_max(d, f, i): 
    if   i > f: return 1, f # C
    if d*i < f: return d, i # A
    w = f//i # B
    q = f-w*i
    if q==0: return w, i+q
    else: return 1+w, q

def v_min(d, f, i): 
    if i >= f: return 1, f # C
    if i >= d: return 1, i # B
    w = d//i # A
    q = d-w*i
    if q==0: return  w, i+q
    else: return 1+w, q

def simu(d, f, x): # x is a speed parameter in [0,100]
    print ('init:%d final:%d speed:%d' % (d, f, x))
    to, po, ko = 0, d, 1
    for i in range(1, f+10):
        p, k   = value(d, f, i, po, ko, x)
        pm, km = v_min(d, f, i)
        pM, kM = v_max(d, f, i)
        t, tm, tM = k*p +(i-k)*(p-1), km*pm +(i-km)*(pm-1), kM*pM +(i-kM)*(pM-1)
        assert p==pm and k==km if x==0 else p==pM and k==kM if x==100 else t>=tm and t<=tM     # POST1 
        assert p>0 and k>0 and k<=i and t>=to and k<=ko if (p==po and k<i) else p<=po and t<=f # POST2
        #assert p>0 and k>0 and k<=i and t>=to and k<=ko if (p==po) else p<=po and t<=f # POST2
        print ('%d: %d*%d+%d*%d=%d' % (i, k, p, i-k, p-1, t))
        to, po, ko = t, p, k

if __name__ == '__main__': # simple check with simulation
    simu(10, 100, 0)
    #for d in range (1, 200): # as an example
    #    for x in range(101): simu(d, 200, x) 
