"""Exact finite C3 isotypic spectral/heat/zeta regression. No physical/RH identification."""
from fractions import Fraction as Q
from math import exp, expm1

def mm(A,B):
    return tuple(tuple(sum(a*b for a,b in zip(row,col)) for col in zip(*B)) for row in A)
def add(A,B):
    return tuple(tuple(a+b for a,b in zip(x,y)) for x,y in zip(A,B))
def scale(q,A):
    return tuple(tuple(q*a for a in row) for row in A)
def trace(A):
    return sum(A[i][i] for i in range(len(A)))
I=((Q(1),Q(0),Q(0)),(Q(0),Q(1),Q(0)),(Q(0),Q(0),Q(1)))
S=((Q(0),Q(1),Q(0)),(Q(0),Q(0),Q(1)),(Q(1),Q(0),Q(0)))
S2=mm(S,S)
P0=scale(Q(1,3),add(add(I,S),S2))
P1=add(I,scale(-1,P0))
def hamiltonian(a=Q(2),b=Q(5)):
    return add(scale(a,P0),scale(b,P1))
def moment(k,a=Q(2),b=Q(5)): return a**k+2*b**k
def sector_moment(k,a=Q(2),b=Q(5)): return a**k,2*b**k
def heat(t,a=2.,b=5.): return exp(-t*a)+2*exp(-t*b)
def sector_heat(t,a=2.,b=5.): return exp(-t*a),2*exp(-t*b)
def twisted_heat(t,a=2.,b=5.): return exp(-t*a)-exp(-t*b)
def spectral_zeta(s,a=2.,b=5.): return a**(-s)+2*b**(-s)
def sector_zeta(s,a=2.,b=5.): return a**(-s),2*b**(-s)
def bose_population(beta,mu=0.,a=2.,b=5.):
    if beta<=0 or mu>=min(a,b): raise ValueError('beta>0, mu<min energies required')
    return 1/expm1(beta*(a-mu)),2/expm1(beta*(b-mu))
def zero_point(hbar=1.,a=2.,b=5.): return hbar*(a+2*b)/2
def certificates():
    H=hamiltonian()
    D=((Q(1),Q(0),Q(0)),(Q(0),Q(2),Q(0)),(Q(0),Q(0),Q(3)))
    return {
      'C3_group_law':mm(S,mm(S,S))==I,
      'P0_idempotent':mm(P0,P0)==P0,
      'P1_idempotent':mm(P1,P1)==P1,
      'P0P1_orthogonal':mm(P0,P1)==scale(0,I),
      'P0_plus_P1_identity':add(P0,P1)==I,
      'sector_ranks_1_2':(trace(P0),trace(P1))==(1,2),
      'H_commutes_S':mm(H,S)==mm(S,H),
      'same_H_sector_spectrum':mm(H,P0)==scale(2,P0) and mm(H,P1)==scale(5,P1),
      'H_squared_trace':trace(mm(H,H))==moment(2),
      'twisted_character':(trace(mm(S,P0)),trace(mm(S,P1)))==(1,-1),
      'negative_control_D_breaks_S':mm(S,D)!=mm(D,S),
    }
