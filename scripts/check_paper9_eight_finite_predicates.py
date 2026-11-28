#!/usr/bin/env python3
"""Independent exact replay of eight Lean finite predicate specifications, not kernel proof."""
from fractions import Fraction as F
from hashlib import sha1
from json import dumps
from time import monotonic
from pathlib import Path
from subprocess import run
from sympy import Poly, symbols, ZZ
P=41; K=-640320**3; D=3322
PACKET='17ed967d83d1aacafdb0f19d7bd81e6afc5887a4'
def conv(a,b,d):
    return [sum(a[i]*b[n-i] for i in range(max(0,n-len(b)+1),min(n+1,len(a)))) for n in range(d+1)]
def unit():
    d=D+1
    s3=[0]*(d+1);s5=[0]*(d+1);s1=[0]*(d+1)
    for i in range(1,d+1):
        for j in range(i,d+1,i):
            s3[j]+=i**3;s5[j]+=i**5;s1[j]+=i
    a=[1]+[240*x for x in s3[1:]];b=[1]+[-504*x for x in s5[1:]]
    a=conv(conv(a,a,d),a,d);b=conv(b,b,d)
    u=[]
    for n in range(D+1):
        q,r=divmod(a[n+1]-b[n+1],1728);assert r==0;u.append(q)
    assert u[0]==1
    j=[a[0]]
    for n in range(1,D+1):j.append(a[n]-sum(u[i]*j[n-i] for i in range(1,n+1)))
    assert all(1728*u[n]==a[n+1]-b[n+1] for n in range(D+1))
    assert conv(u,j,D)==a[:D+1]
    inv=[1]
    for n in range(1,D+1):
        q,r=divmod(sum(24*s1[i]*inv[n-i] for i in range(1,n+1)),n);assert r==0;inv.append(q)
    assert conv(a,inv,D)==j
    return j
def sector(j,diag):
    d=82 if diag else 42;m=P*d
    h=[0]*(m+1);g=[0]*(d+1)
    if diag:
        for i in range(d+1):h[P*i]+=j[i]
        for i in range(m-P+2):h[i+P-1]-=j[i]
        for i in range(d-P+2):g[i+P-1]+=j[i]
        for i in range(d//P+1):g[P*i]-=j[i]
    else:
        h=j[:m+1];h[1]-=K
        for i in range(d//P+1):g[P*i]+=j[i]
        g[P]-=K
    # Independent GMP exact scalar recurrence and scatter residual.
    exe=Path(__file__).with_name("paper9_gmp_residual")
    payload=str(len(h))+"\n"+"\n".join(format(x,"x") for x in h)+"\n"
    result=run([str(exe)],input=payload,text=True,capture_output=True,check=True,timeout=90)
    L=[int(x,16) for x in result.stdout.splitlines()]
    assert len(L)==m+1
    N=[1];v=L[::P]
    for n in range(1,d+1):
        q,r=divmod(sum(v[i]*N[n-i] for i in range(1,n+1)),n);assert r==0;N.append(q)
    assert h[0]==1 and L[0]==0 and N[0]==1
    # GMP helper checked every original convolution coefficient independently.
    assert conv(N,v,d)==[n*N[n] for n in range(d+1)]
    target=conv(g,N,d);rem=target[:]
    powers=[[1]+[0]*d]
    for i in range(d):powers.append(conv(powers[-1],j[:d+1],d))
    coeff=[0]*(d+1)
    for i in range(d,-1,-1):
        c=rem[d-i];coeff[i]=c
        for k in range(i+1):rem[d-i+k]-=c*powers[i][k]
    assert not any(rem)
    replay=[0]*(d+1)
    for i,c in enumerate(coeff):
        for k in range(i+1):replay[d-i+k]+=c*powers[i][k]
    assert replay==target and coeff[-1]==(-1 if diag else 1)
    return coeff
def main():
    start=monotonic();j=unit();print('unitOK: 6646 residuals; 3323 independent eta coefficients PASS',flush=True)
    p=sector(j,True);print('diagOK: 3363 Euler + 83 norm + 83 columns PASS',flush=True)
    s=sector(j,False);print('sliceOK: 1723 Euler + 43 norm + 43 columns PASS',flush=True)
    raw=(dumps([[hex(c) for c in reversed(x)] for x in (p,s)],separators=(',',':'))+'\n').encode()
    blob=sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest();assert blob==PACKET,(blob,len(raw))
    print('literal 126 coefficient packet Git blob matches',blob,flush=True)
    X=symbols('X');p,s=([int(c) for c in reversed(Poly.from_list(list(reversed(x)),X,domain=ZZ).shift(K).all_coeffs())] for x in (p,s))
    assert p[0]==p[1]==0
    assert sum(abs(p[i+3])*2**(79-i) for i in range(80))<abs(p[2])*2**80
    print('shiftOK PASS',flush=True)
    assert s[0]==s[1]==0 and s[2]!=0 and 41*p[2]==163*s[2]
    assert (41*p[3]-326*s[3])*19943834790540897829879824384000==-77859659565707*163*s[2]
    print('jetOK PASS',flush=True)
    scale=2**128
    pl,ph=1069028584064966747859680373161870783300,1069028584064966747859680373161870783301
    sl,sh=4344434433350621975299947493401713860084,4344434433350621975299947493401713860085
    def atan(d,n):return sum((F((-1)**k,(2*k+1)*d**(2*k+1)) for k in range(n)),F(0))
    assert F(pl,scale)<=16*atan(5,90)-4*atan(239,31)
    assert 16*atan(5,91)-4*atan(239,30)<=F(ph,scale)
    print('piRoundOK PASS',flush=True)
    assert sl**2<=163*scale**2<=sh**2
    print('sqrtRoundOK PASS',flush=True)
    lo,hi=F(pl*sl,scale**2),F(ph*sh,scale**2)
    def exp_prefix(x):
        term=F(1);total=F(0)
        for n in range(180):total+=term;term=term*x/(n+1)
        return total,term
    l,_=exp_prefix(lo);h,t=exp_prefix(hi)
    assert 0<=lo<=hi and 2*hi<181
    assert -K+744-F(1,4)<l and h+2*t<-K+744+F(1,4)
    print('expWindowOK PASS; all 8 finite predicate specifications PASS',flush=True)
    print('wall seconds',round(monotonic()-start,3),flush=True)
if __name__=='__main__':main()
