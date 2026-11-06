#!/usr/bin/env python3
"""Exact-rational enclosure of the actual Gielis raster FD *discrete* λ_1.

Reconstruct the same 5-point interior Cartesian grid as
gielis_base369_experiments.laplacian_eigenvalues. Use scipy eigsh ONLY
to propose a positive rational vector x. The final λ_1 bracket is a
mathematical theorem for the finite symmetric M-matrix, independent of
the numerical eigenvalue's correctness:

    min_i ((4 x_i - sum_neighbours x_j)/x_i)/h²
      <= λ_1(A) <=
    max_i ((4 x_i - sum_neighbours x_j)/x_i)/h²,

because the interior nearest-neighbour graph is connected and its
adjacency matrix is irreducible nonnegative; Collatz-Wielandt bounds
its Perron root, and A=(4I-Adj)/h².

This does NOT prove convergence to the Dirichlet eigenvalues on the
continuous Gielis domain; the sectorwise continuum enclosure is a
different approximation and cannot be silently composed with this one.
"""
from __future__ import annotations
from fractions import Fraction as Q
import argparse, json, math
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.linalg import eigsh
import gielis_base369_experiments as G

def certify(m:int,n:int=41,scale:int=10**15)->dict:
    if type(m) is not int or m<=0 or n<17 or n%2!=1 or scale<1000:
        raise ValueError("m>0, odd grid n>=17, scale>=1000 required")
    axis=np.linspace(-1.5,1.5,n)
    x,y=np.meshgrid(axis,axis,indexing="ij")
    inside=np.hypot(x,y)<G.gielis_radius(np.arctan2(y,x),m)-1e-12
    points=np.argwhere(inside)
    index={tuple(map(int,p)):j for j,p in enumerate(points)}
    neighbors=[]
    for i,j in points:
        neighbors.append([index[(int(i)+di,int(j)+dj)]
                          for di,dj in ((1,0),(-1,0),(0,1),(0,-1))
                          if (int(i)+di,int(j)+dj) in index])
    if not neighbors:
        raise ValueError("no interior lattice points")
    seen={0};queue=[0]
    for node in queue:
        for nb in neighbors[node]:
            if nb not in seen:
                seen.add(nb);queue.append(nb)
    if len(seen)!=len(points):
        raise ValueError("interior adjacency disconnected: PF certificate refused")
    rows=[];cols=[];data=[]
    for k,adj in enumerate(neighbors):
        rows.append(k);cols.append(k);data.append(4.)
        for j in adj:
            rows.append(k);cols.append(j);data.append(-1.)
    A=csr_matrix((data,(rows,cols)),shape=(len(points),len(points)))
    evals,vecs=eigsh(A,k=1,which="SA",tol=1e-13,
                     v0=np.ones(len(points)),maxiter=100000)
    v=np.abs(vecs[:,0])
    q=[max(1,int(round(float(z)*scale))) for z in v]
    # Every exact rational test vector entry is STRICTLY POSITIVE.
    ratios=[Q(4*q[k]-sum(q[j] for j in adjacent),q[k])
            for k,adjacent in enumerate(neighbors)]
    h_inv_sq=Q((n-1)**2,9)
    lower=min(ratios)*h_inv_sq
    upper=max(ratios)*h_inv_sq
    if lower<=0:
        raise ValueError("certificate nonpositive; increase rational rounding scale")
    estimate=float(evals[0])*float(h_inv_sq)
    if not float(lower)-1e-9<=estimate<=float(upper)+1e-9:
        raise AssertionError("eigensolver estimate outside exact bracket")
    old=G.laplacian_eigenvalues(m,n,k=4)[0]
    if not float(lower)-1e-8<=old<=float(upper)+1e-8:
        raise AssertionError("original Gielis FD eigsh outside rational bracket")
    return {
        "status":"certified_finite_discrete_lambda1_enclosure",
        "mode":m,"axis_nodes":n,
        "interior_nodes":len(points),"adjacency_connected":True,
        "degree_diagonal":"4","off_diagonal":"-1 for adjacent",
        "h_inv_squared_exact":str(h_inv_sq),
        "all_integer_test_vector_entries_positive":True,
        "integer_vector_scale":scale,
        "rational_lower":str(lower),"rational_upper":str(upper),
        "lower_decimal":float(lower),"upper_decimal":float(upper),
        "certified_interval_width":float(upper-lower),
        "scipy_eigsh_estimate":estimate,
        "original_fd_eigsh_estimate":old,
        "proof":"Collatz-Wielandt/Perron-Frobenius with exact integer vector",
        "original_cartesian_fd_discrete_operator_identified":True,
        "continuum_dirichlet_mesh_convergence_proved":False,
        "sympy_or_agda_needed_for_discrete_certificate":False,
    }

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--m",type=int,default=3)
    p.add_argument("--grid",type=int,default=41)
    p.add_argument("--scale",type=int,default=10**15)
    p.add_argument("--output")
    a=p.parse_args()
    result=certify(a.m,a.grid,a.scale)
    rendered=json.dumps(result,sort_keys=True,indent=2)
    if a.output:
        from pathlib import Path
        Path(a.output).write_text(rendered+"\n")
    print(rendered)

if __name__=="__main__":main()
