#!/usr/bin/env python3
"""Independent polynomial audit of H06 Bishop source formulas; not Agda execution."""
from sympy import Matrix, eye, symbols, expand, cancel

def require(condition, label):
    if not condition: raise RuntimeError(label)
a,b,c,d,u,v,i,w,x,y,z=symbols('a b c d u v i w x y z', real=True)
B=Matrix([[a,b],[c,d]]); D=B.det(); X=Matrix([u,v]); C=i*B.adjugate()*X
require(all(expand(e)==0 for e in B*C-i*D*X),'Cramer forward')
require(all(expand(e)==0 for e in i*B.adjugate()*B*X-i*D*X),'Cramer backward')
N=w*w+x*x+y*y+z*z
M=Matrix([[N-2*(y*y+z*z),2*(x*y-w*z),2*(x*z+w*y)], [2*(x*y+w*z),N-2*(x*x+z*z),2*(y*z-w*x)], [2*(x*z-w*y),2*(y*z+w*x),N-2*(x*x+y*y)]])
require(all(expand(e)==0 for e in M.T*M-N*N*eye(3)),'numerator Gram')
require(expand(M.det()-N**3)==0,'numerator determinant')
R=M/N
require(all(cancel(e)==0 for e in R.T*R-eye(3)),'normalized Gram')
require(cancel(R.det()-1)==0,'normalized determinant')
# Quaternion projective reconstruction, all four charts on their domains.
Q=Matrix([[1+R.trace(),R[2,1]-R[1,2],R[0,2]-R[2,0],R[1,0]-R[0,1]]])/4
q=Matrix([w,x,y,z]); H=q*q.T/N
require(all(cancel(e)==0 for e in Q-H[:1,:]),'first projector row')
for k in range(4):
    require(all(cancel(e)==0 for e in H[:,k]/H[k,k]-q/q[k]),'projective inverse')
print('PASS 4 Cramer identities, 9 numerator Gram, determinant, 9 normalized Gram, determinant, 4 first projector row, 16 projective inverse entries')
