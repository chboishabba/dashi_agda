#!/usr/bin/env python3
"""Fixed BR4 variable-coefficient tangential hierarchy and normal recovery.
Uses a^yy=1, not a small perturbation of frozen principal coefficients."""
import sympy as s
from itertools import combinations_with_replacement
from math import comb

def add(a,b):return tuple(x+y for x,y in zip(a,b))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def multi(k,d):
    if d==1:
        yield (k,);return
    for i in range(k+1):
        for a in multi(k-i,d-1):yield (i,)+a

def le(a,b):return all(x<=y for x,y in zip(a,b))
def check():
    # t,x1,x2,x3,y; y is the fixed cut normal.
    E=[tuple(int(i==j) for i in range(5)) for j in range(5)]
    y=E[-1]; pairs=list(combinations_with_replacement(range(5),2))
    active=[(i,j) for i,j in pairs if (i,j)!=(4,4)]
    n=0
    for order in range(1,9):
        for a0 in multi(order,4):
            a=a0+(0,)
            for k in range(1,order+1):
                for b0 in multi(k,4):
                    b=b0+(0,)
                    if not le(b,a):continue
                    for i,j in active:
                        u=add(sub(a,b),add(E[i],E[j]))
                        assert sum(u)<=order+1 and u[-1]<=1
                        assert any(u[l]>0 for l in range(4))
                        n+=1
        # Recover each piecewise normal jet from a^yy=1.
        for total in range(2,order+2):
            for a in multi(total,5):
                if a[-1]<2:continue
                rhs=sub(a,add(y,y))
                for k in range(sum(rhs)+1):
                    for b in multi(k,5):
                        if not le(b,rhs):continue
                        for i,j in active:
                            u=add(sub(rhs,b),add(E[i],E[j]))
                            assert sum(u)<=total and u[-1]<a[-1]
                            n+=1
                # Lower source depending on first jets: derivatives of those
                # also have lower normal order, at most total-1 derivatives.
                for i in range(5):
                    u=add(rhs,E[i])
                    assert sum(u)==total-1 and u[-1]<a[-1]
    # Direct mixed time/tangential Leibniz expansion, all active matrix entries.
    t,x,y0=s.symbols('t x y'); coord=(t,x,y0)
    u=s.Function('u')(*coord)
    A=s.Matrix(3,3,lambda i,j:s.S.One if i==j==2 else s.Function('a%d%d'%(min(i,j),max(i,j)))(*coord))
    L=lambda v:sum(A[i,j]*s.diff(v,coord[i],coord[j]) for i in range(3) for j in range(3))
    D=lambda v:s.diff(v,t,x)
    R=sum((s.diff(A[i,j],t)*s.diff(u,x,coord[i],coord[j])+s.diff(A[i,j],x)*s.diff(u,t,coord[i],coord[j])+s.diff(A[i,j],t,x)*s.diff(u,coord[i],coord[j])) for i in range(3) for j in range(3))
    assert s.expand(D(L(u))-L(D(u))-R)==0
    print('PASS',n,'tangential commutator and normal recovery index controls through order 8')
    print('PASS direct variable-coefficient mixed Leibniz identity')
if __name__=='__main__':check()
