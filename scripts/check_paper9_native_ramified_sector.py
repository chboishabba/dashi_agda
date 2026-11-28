#!/usr/bin/env python3
"""Independent exact reference replay: not Agda/Lean execution.

Adapt the existing eight-predicate integer recurrence checker, retaining
its GMP residual helper and original packet digest; additionally check
the ramified phase sector and signed rational angles.
"""
from collections import Counter
from hashlib import sha1
from json import dumps
from pathlib import Path
from subprocess import run
from sympy import Poly, symbols, ZZ
P=41; K=-640320**3; D=3322
PACKET='17ed967d83d1aacafdb0f19d7bd81e6afc5887a4'
def conv(a,b,d):
    return [sum(a[i]*b[n-i] for i in range(max(0,n-len(b)+1),min(n+1,len(a)))) for n in range(d+1)]
def unit():
    d=D+1
    s3=[0]*(d+1);s5=[0]*(d+1)
    for i in range(1,d+1):
        for j in range(i,d+1,i):
            s3[j]+=i**3;s5[j]+=i**5
    a=[1]+[240*x for x in s3[1:]];b=[1]+[-504*x for x in s5[1:]]
    a=conv(conv(a,a,d),a,d);b=conv(b,b,d)
    u=[]
    for n in range(D+1):
        q,r=divmod(a[n+1]-b[n+1],1728);assert r==0;u.append(q)
    assert u[0]==1
    j=[a[0]]
    for n in range(1,D+1):j.append(a[n]-sum(u[i]*j[n-i] for i in range(1,n+1)))
    assert conv(u,j,D)==a[:D+1]
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
    exe=Path(__file__).with_name('paper9_gmp_residual')
    payload=str(len(h))+'\n'+'\n'.join(format(x,'x') for x in h)+'\n'
    result=run([str(exe)],input=payload,text=True,capture_output=True,check=True,timeout=90)
    L=[int(x,16) for x in result.stdout.splitlines()]
    assert len(L)==m+1
    N=[1];v=L[::P]
    for n in range(1,d+1):
        q,r=divmod(sum(v[i]*N[n-i] for i in range(1,n+1)),n);assert r==0;N.append(q)
    assert h[0]==1 and L[0]==0 and N[0]==1
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

def phase():
    z=symbols('z');phi=Poly(sum(z**i for i in range(P)),z,domain=ZZ)
    for n in range(3363):
        counts=Counter((n*k)%P for k in range(P))
        if n%P==0:assert counts=={0:P}
        else:assert counts==dict.fromkeys(range(P),1)
    for k in range(1,P):
        assert not Poly(z**k-1,z,domain=ZZ).rem(phi).is_zero
        a=2*k if k<=20 else 2*k-P
        assert 0<a<P
    assert sum(range(P))%P==0
    assert (-1)**P==-1 and P*82==3362 and P*42==1722
    print('phase: 3363 trace sectors, 40 primitive and 40 signed angle checks PASS',flush=True)

def main():
    phase()
    j=unit();print('3323 normalized discriminant and j coefficients PASS',flush=True)
    p=sector(j,True);print('diagonal: 3363 Euler, 83 norm, 83 column coefficients PASS',flush=True)
    s=sector(j,False);print('slice: 1723 Euler, 43 norm, 43 column coefficients PASS',flush=True)
    raw=(dumps([[hex(c) for c in reversed(x)] for x in (p,s)],separators=(',',':'))+'\n').encode()
    blob=sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
    assert blob==PACKET,(blob,len(raw))
    print('literal 126 coefficient packet Git blob matches',blob,flush=True)
    X=symbols('X');p,s=([int(c) for c in reversed(Poly.from_list(list(reversed(x)),X,domain=ZZ).shift(K).all_coeffs())] for x in (p,s))
    assert p[0]==p[1]==s[0]==s[1]==0 and s[2]!=0
    assert sum(abs(p[i+3])*2**(79-i) for i in range(80))<abs(p[2])*2**80
    assert 41*p[2]==163*s[2]
    assert (41*p[3]-326*s[3])*19943834790540897829879824384000==-77859659565707*163*s[2]
    print('literal shifted diagonal/slice, dominance, quadratic and signed cubic jet PASS',flush=True)
if __name__=='__main__':main()
