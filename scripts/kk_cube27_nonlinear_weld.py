"""Selected anisotropic charging vertex; exact perturbation recursion for finite H.
No identification of q with actual CY modulus: prescribed local radius profile.
"""
from kk_cube27_manypair_bidi import operators
import numpy as np
from scipy.sparse import diags
from scipy.sparse.linalg import eigsh,cg,LinearOperator

def weld(N,U,flux):
 H,Q,O,S=operators(N,U,1,flux)
 e,w=eigsh(H,k=2,which='SA',tol=1e-12,v0=np.ones(H.shape[0])); i=np.argsort(e); e=e[i];g=w[:,i[0]]
 assert e[1]-e[0]>1e-7
 def project(x): return x-g*np.vdot(g,x)
 A=LinearOperator(H.shape,matvec=lambda x:H@x-e[0]*x+g*np.vdot(g,x),dtype=complex)
 def G(x):
  y,info=cg(A,project(x),rtol=1e-11,maxiter=2000); assert info==0
  return project(y)
 # H(E)=H-E O, intermediate-normalization Taylor recursion.
 v=[g]; coeff=[e[0]]
 for n in range(1,5):
  coeff.append(-np.vdot(g,O*v[n-1]).real)
  if n<4:
   v.append(G(O*v[n-1]+sum(coeff[j]*v[n-j] for j in range(1,n+1))))
 assert abs(coeff[1])+abs(coeff[3])<1e-8
 chi=-2*coeff[2]; beta=4*coeff[4]/chi**4
 # local q_i=q z_i; U_i(q)=U exp(-3q_i/2), evaluated at q=0.
 # mixed derivative uses linearized vertex A_q=-3U S/2, exact at origin.
 Aq=-1.5*U*S
 mixed=2*np.vdot(project(Aq*g),G(O*g)).real
 def energy(f,q):
  return eigsh(H+diags(f*O+q*Aq),k=1,which='SA',v0=g,tol=1e-12,return_eigenvectors=False)[0]
 for h in (0.002,0.001):
  fd=-(energy(h,h)-energy(h,-h)-energy(-h,h)+energy(-h,-h))/(4*h*h)
  assert abs(fd-mixed)<2e-5
 # Derivative of symmetric constitutive coefficients, no cubic term by z reflection.
 # Positive beta is a local coefficient, not the global potential stability criterion.
 print(N,U,flux,'chi',chi,'beta',beta,'mixed',mixed,'fd',fd,flush=True)
 return chi,beta,mixed
if __name__=='__main__':
 for N in (2,3):
  for U in (1,4):
   for flux in (0,1.5):weld(N,U,flux)
 print('PASS fourth-order reduced-resolvent recursion and independent mixed-vertex checks')
