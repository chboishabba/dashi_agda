#!/usr/bin/env python3
"""Exact equality-chart replay; not an Agda kernel proof."""
from collections import Counter
from sympy import symbols, expand, summation, divisor_sigma, __version__

a,b,d,t=symbols('a b d t', integer=True)
Q=lambda a,b:a*a-a*b+b*b
weights=[Q,lambda a,b:Q(a,b)**2,lambda a,b:Q(a,b)**3,lambda a,b:a*a*b*b*(a-b)**2]
closed=[(5*d**3-6*d**2+d)/6,(21*d**5-30*d**4+10*d**3-d)/30,(249*d**7-420*d**6+210*d**5-49*d**3+10*d)/420,(d**7-d**3)/30]
for f,c in zip(weights,closed):
    assert expand(summation(f(d,d-t),(t,1,d-1))-c)==0

def factors(n):
    return [(d,n//d) for d in range(1,n+1) if n%d==0]

def xy(d,k,t):return (t,d-t,k,k)
def ab(d,k,t):return (d,d,t,k-t)
def xy_key(q):
    a,b,x,y=q;assert x==y;return (a+b,x,a)
def ab_key(q):
    a,b,x,y=q;assert a==b;return (a,x+y,x)

def main():
    points=nx=na=both=folds=0
    for n in range(1,129):
        omega=[(a,b,x,y) for i in range(1,n) for a,x in factors(i) for b,y in factors(n-i)]
        X=[q for q in omega if q[2]==q[3]]; A=[q for q in omega if q[0]==q[1]]
        xc=[(d,k,t) for d,k in factors(n) for t in range(1,d)]
        ac=[(d,k,t) for d,k in factors(n) for t in range(1,k)]
        assert Counter(map(lambda z:xy(*z),xc))==Counter(X)
        assert Counter(map(lambda z:ab(*z),ac))==Counter(A)
        assert all(xy_key(xy(*z))==z for z in xc)
        assert all(ab_key(ab(*z))==z for z in ac)
        assert all(xy(*xy_key(q))==q for q in X)
        assert all(ab(*ab_key(q))==q for q in A)
        assert len(set(X))==len(X) and len(set(A))==len(A)
        I=set(X)&set(A); expected={(d,d,k,k) for d,k in factors(n//2)} if n%2==0 else set()
        assert I==expected
        sig=lambda u:sum(d**u for d,k in factors(n))
        for j,(f,c) in enumerate(zip(weights,closed)):
            assert sum(f(a+b,b) for a,b,x,y in X)==sum(c.subs(d,z) for z,k in factors(n))
            assert sum(f(a,b) for a,b,x,y in A)==(n*sig(2*j+1)-sig(2*j+2) if j<3 else 0)
            folds+=2
        points+=len(omega);nx+=len(X);na+=len(A);both+=len(I)
    print(f'SymPy {__version__}; 4 symbolic boundary sums; 128 grades; {points} points; XY {nx}; AB {na}; intersection {both}; {folds} folds PASS')
if __name__=='__main__':main()
