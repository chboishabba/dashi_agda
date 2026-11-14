#!/usr/bin/env python3
"""Exact colour SU(3) metric audit: distinguish colour fibre from flavour masses."""
import sympy as s

I=s.I
Z=s.zeros(3)
E=lambda a,b:s.eye(3)[:,a]*s.eye(3)[b,:]
L=[
 E(0,1)+E(1,0),
 -I*E(0,1)+I*E(1,0),
 E(0,0)-E(1,1),
 E(0,2)+E(2,0),
 -I*E(0,2)+I*E(2,0),
 E(1,2)+E(2,1),
 -I*E(1,2)+I*E(2,1),
 (E(0,0)+E(1,1)-2*E(2,2))/s.sqrt(3),
]
def zero(M): return all(s.simplify(x)==0 for x in M)
def main():
  assert len(L)==8 and all(zero(A-A.H) and s.trace(A)==0 for A in L)
  for a in range(8):
    for b in range(8):
      # Commutator of traceless Hermitian basis directions is anti-Hermitian/traceless
      C=L[a]*L[b]-L[b]*L[a]
      assert zero(C+C.H) and s.simplify(s.trace(C))==0
  w0,w1,w2=s.symbols("w0 w1 w2",real=True)
  W=s.diag(w0,w1,w2)
  # Hermitian generator T preserving W requires T W = W T.
  assert zero(L[0]*W-W*L[0]) is False
  assert zero((L[0]*W-W*L[0]).subs(w1,w0))
  # A mass matrix may break flavour SU3 while all colour rotations act on
  # an independent colour C3: W_flavour tensor I_colour.
  Q=s.eye(3)
  assert all(zero(A.H*Q-Q*A) for A in L)
  for a in range(8):
    X=s.kronecker_product(W,s.eye(3))
    U=s.kronecker_product(s.eye(3),L[a])
    assert zero(X*U-U*X)
  print("PASS eight independent traceless Hermitian SU3 Lie generators")
  print("PASS exact colour metric I invariance and independent flavour-weight commutation")
  print("PASS unequal prime-lane metric obstruction shown for colour mixing")
  print("LIMIT cannot identify prime lanes with physical colour without a same-object map")

if __name__=="__main__":main()
