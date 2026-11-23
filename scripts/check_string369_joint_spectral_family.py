import numpy as np
from scipy.linalg import eigh
import sympy as s
# Original restricted V6 Hessian, inherited finite Gram; conditional, not physical CY identification.
r=.201971182865772;t=.0246;x=np.sqrt(1-t*t/2);y=np.sqrt(1-2*t*t);D=1-r*r
H=np.array([[8*x*x,0,4*x*t],[0,8*y*y,16*y*t],[4*x*t,16*y*t,40*t*t]])
G=np.array([[1,r,0],[r,1,0],[0,0,D]])
a=eigh(H,eigvals_only=True);q=a[0]*D**(2/3);A=H[:2,:2]-q*G[:2,:2];b=H[:2,2];N=b@np.linalg.inv(A)@b;d=np.linalg.det(A)
gmax=np.sqrt((d-d*N/(H[2,2]-q*D))/(4*q))
for g in [0,1,2,3,4,5,6,7,gmax]:
 h=q*D+N*d/(d-4*q*g*g);dl=(h-H[2,2])/(8*t*t);HH=H.copy();HH[2,2]=h;O=np.array([[0,-g,0],[g,0,0],[0,0,0]]);T=np.block([[np.zeros((3,3)),np.eye(3)],[-np.linalg.solve(G,HH),-2*np.linalg.solve(G,O)]]);ev=np.linalg.eigvals(T);w=np.sort(ev.imag[ev.imag>0]);assert max(abs(ev.real))<1e-10 and abs(w[0]**2-q)<1e-10
 assert np.isclose(np.prod(w**2),np.linalg.det(HH)/np.linalg.det(G))
 assert np.isclose(np.sum(w**2),np.trace(np.linalg.solve(G,HH))-2*np.trace(np.linalg.matrix_power(np.linalg.solve(G,O),2)))
 print(g,4+dl,w,np.prod(w[1:]))
# exact characteristic factor and product invariant
u,v,c,f,j,k,g,z=s.symbols('u v c f j k g z',real=True)
B=s.Matrix([[u,c-2*s.I*z*g,f],[c+2*s.I*z*g,v,j],[f,j,k]])
assert s.expand(B.det()-(k*(u*v-c*c-4*z*z*g*g)-(v*f*f-2*c*f*j+u*j*j)))==0
print('PASS exact pole identity and spectral sum/product; OPEN rotational source and physical action')
