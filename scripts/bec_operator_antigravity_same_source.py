"""Finite same-source operator equivalence + Lorentz stress sign firewall.

An inhabited three-dimensional rational Hilbert-space *model*. Not an
empirically selected OS/KK physical Hamiltonian or measured antigravity source.
Original research authority: standard finite spectral theory; reuse
DASHI.Physics.Foundations.CMP119AntigravityTraceVsActiveStressFirewallExact.
"""
from fractions import Fraction as Q
from math import exp

I=((Q(1),Q(0),Q(0)),(Q(0),Q(1),Q(0)),(Q(0),Q(0),Q(1)))
S=((Q(0),Q(1),Q(0)),(Q(0),Q(0),Q(1)),(Q(1),Q(0),Q(0)))
U=((Q(0),Q(1),Q(0)),(Q(1),Q(0),Q(0)),(Q(0),Q(0),Q(1)))
def T(A): return tuple(zip(*A))
def mul(A,B): return tuple(tuple(sum(x*y for x,y in zip(row,col)) for col in zip(*B)) for row in A)
def add(A,B): return tuple(tuple(x+y for x,y in zip(row,col)) for row,col in zip(A,B))
def scale(x,A): return tuple(tuple(x*y for y in row) for row in A)
def trace(A): return sum(A[i][i] for i in range(len(A)))
P0=scale(Q(1,3),add(add(I,S),mul(S,S)))
P1=add(I,scale(-1,P0))
H=add(scale(2,P0),scale(5,P1))
Hobs=mul(mul(U,H),T(U))
Sobs=mul(mul(U,S),T(U))
def intertwines(): return mul(U,H)==mul(Hobs,U)
def power(A,k):
    B=I
    for _ in range(k): B=mul(B,A)
    return B
def sector_moment(k): return trace(mul(P0,power(H,k))),trace(mul(P1,power(H,k)))
def sector_heat(t): return exp(-2*t),2*exp(-5*t)
def sector_zeta(s): return 2**(-s),2*5**(-s)
def stress(rho,px,py,pz): return -rho+px+py+pz,rho+px+py+pz
def checks():
    return {
      "group":power(S,3)==I,
      "projectors":mul(P0,P0)==P0 and mul(P1,P1)==P1 and mul(P0,P1)==scale(0,I),
      "orthogonal_U":mul(U,T(U))==I,
      "whole_operator_intertwining":intertwines(),
      "powers_intertwine":all(mul(U,power(H,n))==mul(power(Hobs,n),U) for n in range(12)),
      "symmetry_intertwines":mul(U,S)==mul(Sobs,U),
      "full_sector_traces":all(sector_moment(n)==(Q(2)**n,2*Q(5)**n) for n in range(10)),
      "one_sector_not_whole_H":mul(H,P0)==mul(add(H,P1),P0) and H!=add(H,P1),
      "negative_trace_not_negative_active":stress(Q(3),0,0,0)==(Q(-3),Q(3)),
      "negative_active_possible_positive_G":stress(Q(1),Q(-1),Q(-1),Q(-1))[1]<0,
      "active_equals_trace_plus_twice_rho":all(stress(r,p,0,0)[1]==stress(r,p,0,0)[0]+2*r for r,p in [(Q(1),Q(4)),(Q(3),0),(Q(-1),Q(2))]),
    }
if __name__=="__main__":
    import json
    results=checks()
    print(json.dumps({"passed":all(results.values()),"checks":results},indent=2))
    if not all(results.values()): raise SystemExit(1)
