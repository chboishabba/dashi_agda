#!/usr/bin/env python3
"""Exact source-shaped coordinate replay, not a Lean/Agda proof receipt."""
from math import isqrt
from sympy import symbols, expand

A, B, C, K = 13591409, 545140134, 640320**3, 426880

def add(x, y):
    a,b=x; c,d=y
    return a*d+c*b,b*d

def mul(x, y):
    a,b=x; c,d=y
    return a*c,b*d

def neg(x): return -x[0],x[1]

def source_pow(x,n):
    # The raw recurrence has exact numerator and denominator powers.
    return x[0]**n,x[1]**n

def lean_term(n):
    o=2*n+1
    a=o*5**o; b=o*239**o
    return (-1)**n*(16*b-4*a),a*b

def source_term(n):
    o=2*n+1
    sign=source_pow((-1,1),n)
    def atan(d): return mul(sign,mul((1,o),source_pow((1,d),o)))
    return add(mul((16,1),atan(5)),neg(mul((4,1),atan(239))))

def lean_prefix(n):
    p=q=1; t=0
    for j in range(n):
        pj=1 if j==0 else -24*(2*j-1)*(6*j-5)*(6*j-1)
        qj=1 if j==0 else C*j**3
        p*=pj; q*=qj; t=t*qj+p*(A+B*j)
    return p,q,t

def source_prefix(n):
    p=q=b=1; t=0
    for j in range(n):
        if j==0: pj=qj=1
        else:
            i=j-1
            pj=-24*(2*i+1)*(6*i+1)*(6*i+5)
            qj=C*(i+1)**3
        p,q,b,t=p*pj,q*qj,b*1,t*qj*1+p*b*((A+B*j)*pj)
    return p,q,b,t

def window(n,s,r,prefix):
    _,q,t=prefix(n); _,q1,t1=prefix(n+1)
    assert t>0 and t1>0 and q>0 and q1>0
    x=(q,t); y=(q1,t1)
    low,high=(x,y) if t*q1<=t1*q else (y,x)
    def corner(rad,v): return K*rad*v[0],s*v[1]
    return corner(r,high),corner(r+1,low)

def cross(x,y,e):
    a,b=x; c,d=y; f,g=e
    assert b>0 and d>0 and g>0
    return a*d*g<=(c*g+f*d)*b

def source_view(n):
    p,q,b,t=source_prefix(n)
    assert b==1
    return p,q*b,t

s,a,b,c,d,e,f,g,h=symbols('s a b c d e f g h')
assert expand((16*s)*b-(4*s)*a-s*(16*b-4*a))==0
assert expand((a*d+c*b)*f-(a*(d*f)+c*(b*f)))==0
assert expand((a*d+c*b)*g+(e*(b*d))*h - (a*d*g+c*b*g+e*b*d*h))==0
print('3 symbolic signed-coordinate identities PASS',flush=True)

m_src=m_lean=(0,1); stages=0; bounds=0; ties=0
for k in range(257):
    n=1+(k+4)//41; scale=2**(k+2); rad=isqrt(10005*scale**2)
    assert rad*rad<=10005*scale**2<(rad+1)**2
    assert lean_prefix(n)==source_view(n)
    assert lean_prefix(n+1)==source_view(n+1)
    l,u=window(n,scale,rad,lean_prefix)
    assert (l,u)==window(n,scale,rad,source_view)
    assert m_src==m_lean
    r=(22,7) if k==0 else (4,25**k)
    assert cross(l,m_src,r) and cross(m_src,u,r)
    bounds+=2
    t1,t2=lean_term(k),source_term(k)
    assert t1==t2 and t1[1]>0 and (t1[0]>0)==(k%2==0)
    stages+=1
    m_lean=add(m_lean,t1); m_src=add(m_src,t2)
    if k%64==0: print('checkpoint',k,flush=True)
# Equality/touching and negative stage-order controls.
assert cross((1,2),(1,3),(1,6))
assert not cross((1,2),(1,3),(1,7))
assert cross((-1,2),(-2,3),(1,6))
assert not cross((-1,2),(-2,3),(1,7))
assert cross((0,1),(0,1),(0,1))
assert cross((0,2),(0,3),(0,5))
print(f'{stages}/{stages} literal raw term/stage + root + window coordinates PASS; {bounds}/{bounds} signed inequalities PASS; 6 boundary controls PASS',flush=True)
