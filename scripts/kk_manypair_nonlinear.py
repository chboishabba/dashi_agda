from kk_manypair_bidi import operators
import numpy as np
from scipy.linalg import eigh
from math import pi
# Symmetry permits q P^2, even when q P is forbidden.
for N in (3,6,9):
 for f in (0,.9,.99):
  H,O,Q,V,C=operators(N,1,1,f*pi/3)
  def susceptibility(q):
   A=H+(np.exp(-1.5*q)-1)*Q
   e,w=eigh(A); a=w[:,1:].conj().T@O@w[:,0]
   return 2*np.sum(abs(a)**2/(e[1:]-e[0]))
  h=1e-4;c=susceptibility(0);vertex=(1/susceptibility(h)-1/susceptibility(-h))/(2*h)
  h2=h/2; v2=(1/susceptibility(h2)-1/susceptibility(-h2))/(2*h2)
  assert abs(vertex-v2)<1e-5
  print(N,f,c,vertex)
print('PASS nonlinear invariant vertex refinement')
