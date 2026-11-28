#!/usr/bin/env python3
"""BR84: source-owned BN/BE/AK initial spatial wall -> full 4D timelike Israel corner.

At a time-symmetric Cauchy slice K_Cauchy=0, choose zero shift at the
initial spacetime-wall intersection and a timelike material wall with
matched lapse N>0 and Riemannian spatial induced wall metric H_AB>0.

The spacetime induced metric is h4=diag(-N²,H_3), and the wall normal
is spatial. With the BR59 convention Kwall=(1/2)L_normal h4,
 Kwall_tt=-N partial_normal N, Kwall_AB=1/2 partial_normal H_AB.
The full pure-tension Israel condition [Kwall_ab]=j h4_ab is therefore
BIDI equivalent to:
    [Kwall_AB]=j H_AB  (existing BE/BN spatial Israel source)
    [partial_normal log N]=j (existing BE/P0AK Hermite lapse corner).
There is NO extra independent scalar jump to solve at this corner.
The full trace reversal gives
 [K]-h tr_h[K] = -3j h in 4 wall dimensions.

For nonzero Cauchy extrinsic K_init or nonzero shift, the mixed
Kwall_tA components and time/material graph must also be paid:
the time-symmetric construction cannot be promoted to general data.

The check uses 3x3 non-diagonal positive H and independent lapse/
normal derivatives, and actually evaluates all 10 timelike-wall
symmetric Israel components and the inverse trace-reversal.

These are source-geometry identities; BN's conditional classical
solution and BE corner must supply the physical representatives.
"""
import argparse
import sympy as s
R=s.Rational

def make():
    H=s.Matrix([[3,1,0],[1,4,1],[0,1,2]])
    assert all(H[:i,:i].det()>0 for i in range(1,4))
    N=R(7,5)
    j=-R(6,5)
    h4=s.diag(-N*N,1,1,1)
    h4[1:4,1:4]=H
    plusN=R(2,7);minusN=plusN-j*N
    # coordinate normals identify the SAME physical unit wall
    # orientation at the paired seam; source includes fixed h.
    Kp=s.zeros(4); Km=s.zeros(4)
    Kp[0,0]=-N*plusN
    Km[0,0]=-N*minusN
    S=s.Matrix([[2,1,0],[1,0,1],[0,1,3]])
    Kp[1:4,1:4]=S+j*H/2
    Km[1:4,1:4]=S-j*H/2
    return H,N,j,h4,Kp,Km,plusN,minusN

def corner():
    H,N,j,h,Kp,Km,plusN,minusN=make()
    jump=Kp-Km
    assert jump==j*h
    assert plusN-minusN==j*N
    tr=s.trace(h.inv()*jump)
    assert tr==4*j
    israel=jump-tr*h+3*j*h
    assert israel==s.zeros(4)
    independent=[israel[a,b] for a in range(4) for b in range(a,4)]
    assert len(independent)==10 and all(z==0 for z in independent)
    print('PASS BR84 BN spatial Israel + BE log-lapse Hermite -> all ten physical timelike-wall Israel equations')

def inverse():
    H,N,j,h,Kp,Km,plusN,minusN=make()
    jump=Kp-Km
    trace=s.trace(h.inv()*jump)
    I=jump-h*trace+3*j*h
    # Same full physical source-dependent inverse as BR63
    K=(I-3*j*h)-h*s.trace(h.inv()*(I-3*j*h))/3
    assert K==jump
    # The spatial source cannot solve the lapse jump by itself.
    bad=Km.copy();bad[0,0]=Kp[0,0]
    missing=(Kp-bad)-j*h
    assert missing[0,0]!=0
    assert missing[1:4,1:4]==s.zeros(3)
    print('PASS BR84 bidirectional full geometric Israel reverse-solve and missing-lapse corner refusal')

def negative():
    H,N,j,h,Kp,Km,plusN,minusN=make()
    # A mixed timelike/spatial wall mode absent from time-symmetric
    # zero-shift initial data is a real extra corner condition.
    source=Kp.copy()
    source[0,1]=source[1,0]=R(1,9)
    mismatch=(source-Km)-j*h
    assert mismatch[0,1]==R(1,9)
    print('PASS BR84 nonzero mixed shift/velocity corner is NOT paid by scalar BN or log-lapse alone')

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--part',choices=['corner','inverse','negative'],default='corner')
    {'corner':corner,'inverse':inverse,'negative':negative}[ap.parse_args().part]()
