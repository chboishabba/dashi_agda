"""Rational weak-load enclosures for exact decimal meshes, not PDE error bounds."""
from fractions import Fraction as F
from math import factorial, ceil

S=1<<80
POLY=((6,81,-92,-46,70,-15),(6,54,-109,58,-7),(24,-36,12,1))
SCALE=(F(8,5),F(32,7),F(16,35))

def floor(x): return x.numerator//x.denominator

def expneg(x):
    assert x>=0
    k=0
    while x>1: x/=2; k+=1
    t=F(1); p=t
    for n in range(1,25):
        t=-t*x/n; p+=t
    lo=floor(S*(p-t*x/25)); hi=ceil(S*p)
    for _ in range(k): lo=lo*lo//S; hi=(hi*hi+S-1)//S
    return F(lo,S),F(hi,S)

def mul(a,b):
    z=[x*y for x in a for y in b]; return min(z),max(z)

def poly(p,a,b):
    y=(F(p[0]),F(p[0]))
    for c in p[1:]:
        l,h=mul(y,(a,b)); y=l+c,h+c
    return y

def common(v):
    l,h=expneg(1/v-1); return l/v**8,h/v**8

def bounds(a,b,q):
    v0,v1=1-b*b,1-a*a
    l0,h0=common(v0); l1,h1=common(v1)
    hi=max(h0,h1)
    if v0<=F(1,8)<=v1: hi=max(hi,common(F(1,8))[1])
    p=poly(POLY[q],a*a,b*b)
    return mul(mul(p,(min(l0,l1),hi)),(SCALE[q]*a**(2+4*q),SCALE[q]*b**(2+4*q)))

def enclose(h,parts=128):
    n=ceil(1/h); cut=F(99,100); out=[[[F(0),F(0)] for _ in range(n+1)] for q in range(3)]
    for j in range(n):
        a,b=j*h,(j+1)*h; c=min(b,cut)
        if c>a:
            for k in range(parts):
                x=a+(c-a)*k/parts; y=a+(c-a)*(k+1)/parts
                r0=(x*x-a*a)/(b*b-a*a); r1=(y*y-a*a)/(b*b-a*a)
                for q in range(3):
                    z=bounds(x,y,q)
                    for i,hat in ((j,(1-r1,1-r0)),(j+1,(r0,r1))):
                        l,u=mul(z,hat); out[q][i][0]+=(y-x)*l; out[q][i][1]+=(y-x)*u
        length=max(F(0),min(b,F(1))-max(a,cut))
        if length:
            for q in range(3):
                e=3*SCALE[q]*sum(map(abs,POLY[q]))*factorial(50)*F(1,50)**42*length
                for i in (j,j+1): out[q][i][0]-=e; out[q][i][1]+=e
    return out

def main():
    import numpy as np
    from ksw668_f8_weak_source import weak_source
    for h in (F(1,5),F(3,20)):
        a=enclose(h,32); b=enclose(h,64); n=ceil(1/h); r=np.arange(n+2)*float(h)*.04
        src=weak_source(.04,r,float(h)*.04)
        for q in range(3):
            d=3+4*q; widths=[]
            for i,(l,u) in enumerate(b[q]):
                assert a[q][i][0]<=l<=u<=a[q][i][1]
                W=((i*h+h/2)**d-max(F(0),i*h-h/2)**d)/d
                val=F(float(src[q,i]))*W
                assert l<=val<=u
                widths.append(float(u-l))
            print(str(h),2*q,max(widths),flush=True)
    print('PASS nested exact rational enclosures and floating producer membership on A/C')
if __name__=='__main__':main()
