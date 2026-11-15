#!/usr/bin/env python3
"""Conservative exact-shell radial FV for KSW original a=t TT multipoles.

In effective d=3,7,11 radial coordinates:
L_h u_j = [r_+^(d-1)(u_(j+1)-u_j) -
           r_-^(d-1)(u_j-u_(j-1))]/(dr*((r_+^d-r_-^d)/d)).
This is NOT the old centre-volume formula.
L_h r^2=2d exactly for every interior cell, and the weighted energy
sum_j W_j u_j L_h u_j=-sum_(faces) A_face (du)^2/dr <=0
for homogeneous remote Dirichlet. Physical retarded acceptance OPEN.
"""
import json
import numpy as np

def coefficients(d,j):
    if not (isinstance(d,int) and isinstance(j,int) and d>=3 and j>=1):
        raise ValueError('integer radial dimension d>=3, cell j>=1')
    p=j+.5;m=j-.5;den=p**d-m**d
    return d*p**(d-1)/den,d*m**(d-1)/den

def old_coefficients(d,j):
    return (1+.5/j)**(d-1),(1-.5/j)**(d-1)

def apply_radial(d,values,dr=1.):
    if dr<=0 or len(values)<4:raise ValueError('finite radial mesh')
    u=np.asarray(values,dtype=float);out=np.zeros_like(u)
    out[0]=2*d*(u[1]-u[0])/dr**2
    for j in range(1,len(u)-1):
        cp,cm=coefficients(d,j)
        out[j]=(cp*(u[j+1]-u[j])-cm*(u[j]-u[j-1]))/dr**2
    return out

def discrete_green_energy(d,values,dr=1.):
    u=np.asarray(values,dtype=float)
    if u[-1]!=0:raise ValueError('homogeneous outer Dirichlet')
    lap=apply_radial(d,u,dr);j=np.arange(len(u),dtype=float)
    vol=(((j+.5)*dr)**d-(np.maximum(j-.5,0)*dr)**d)/d
    lhs=float(np.dot(vol[:-1]*u[:-1],lap[:-1]))
    faces=((np.arange(len(u)-1)+.5)*dr)**(d-1)
    rhs=float(-np.sum(faces*np.diff(u)**2/dr))
    return lhs,rhs

def audit():
    rows=[]
    for d in (3,7,11):
        vals=np.arange(10,dtype=float)**2
        lap=apply_radial(d,vals)
        old=3*old_coefficients(d,1)[0]-old_coefficients(d,1)[1]
        assert np.allclose(lap[:-1],2*d,rtol=5e-13,atol=5e-13)
        rng=np.random.default_rng(d);u=rng.standard_normal(12);u[-1]=0.
        lhs,rhs=discrete_green_energy(d,u)
        assert abs(lhs-rhs)<1e-10*max(abs(rhs),1)
        rows.append(dict(d=d,old_first_cell_r2=old,
          corrected_first_cell_r2=float(lap[1]),exact_r2=2*d,
          green_identity_relative_error=abs(lhs-rhs)/abs(rhs)))
    return dict(original_angular_modes=[0,2,4],effective_dimensions=[3,7,11],
      exact_quadratic_consistency=True,weighted_green_energy_identity=True,
      rows=rows,physical_retarded_Weyl_convergence=False,
      pinned_Agda_kernel_accepted=False)
if __name__=='__main__':print(json.dumps(audit(),indent=2))
