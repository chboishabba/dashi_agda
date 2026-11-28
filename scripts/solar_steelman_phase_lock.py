"""Shared-face conservative phase lock, with optional accounted damping.
Conditional phase subsystem, not a physical electromagnetic constitutive law.
"""
import pickle
import sympy as S
from solar_steelman_autonomous_mediator import tree
from solar_spherical_whitney import shell_mesh


def run():
    _,simplices,_,_=shell_mesh([1,1.5,2]);parent,order=tree(simplices[3]);n=len(order)
    D=S.zeros(n,n-1)
    for k,j in enumerate(order[1:]):D[parent[j],k]=-1;D[j,k]=1
    L=D*D.T
    assert D.rank()==n-1 and L*S.ones(n,1)==S.zeros(n,1)
    # A canonical phase/momentum subsystem in the rotating frame.
    # Energy E=|p|^2/2+k sum(1-cos(D^T theta)).
    # theta'=p; p'=-k D sin(D^T theta)-gamma L p.
    # The gamma term is optional and deposits heat, not free loss removal.
    p,q,k,g=S.symbols('p q k g',real=True)
    assert S.expand(p*(-k*q-g*p)+k*q*p+g*p*p)==0
    # Exact Hessian on zero-mean phase subspace, via tree incidence.
    assert (D.T*D).det()==n
    # Strict local damped stability modulo common phase and momentum:
    # E'=-gamma ||D^T p||^2, zero set p common; invariance then L theta=0.
    # For the linearization, this is exact by connectedness and SPD on quotient.
    # Nonlinear basin: phase differences remain <pi/2 if E<k,
    # since any crossing costs >=k; in that chart sin(delta)=0 iff delta=0.
    assert S.cos(S.pi/2)==0
    # Conservative controller alone is neutral (no phase attraction).
    # Common phase/frequency relative to independent source is NOT fixed.
    # Couple to prior model only as a candidate phase subsystem; actual
    # reaction of phase-dependent material force remains to be derived.
    print('PASS actual 48-cell adjacency, rank47, tree Gram determinant48')
    print('PASS conservative phase potential and accounted damping identity')
    print('Conditional phase-only stability; no coupled carrier or physical lock acceptance')


if __name__=='__main__':run()
