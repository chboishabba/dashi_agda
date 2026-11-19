#!/usr/bin/env python3
"""Actual selected Tian-Yau quotient Gram and two-Higgs contraction.
Original Johl Brown/DASHI selected Jacobian equations and E6 first-Tits
owners; classical quotient inner product, SVD, cyclic characters.
Factorial polynomial norm is a selected finite candidate, not CY L2 metric.
"""
from pathlib import Path
from math import factorial,prod
import runpy
import sympy as s
import numpy as np
d=runpy.run_path(str(Path(__file__).with_name('check_string369_tian_yau_jacobian_cubic_exact.py')))
m1,r1,P,I,V=[d[k] for k in ('m1','r1','P','I','V')]
slice=d['slice'];n=23
R=s.Matrix.hstack(*(s.Matrix(r1[j]) for j in range(len(m1))))
Wi=s.diag(*[s.Rational(1,prod(factorial(k) for k in m)) for m in m1])
G=(R*Wi*R.T).inv();L=Wi*R.T*G
assert R*L==s.eye(n) and L.T*Wi.inv()*L==G and P.T*G*P==G
h1=I[0];h2=sum(I,s.zeros(n,1))
A=V.T*slice(h1)*V;B=V.T*slice(h2)*V
assert A.rank()==B.rank()==14
Z=-A.inv()*B
Krat=s.Matrix.vstack(Z,s.eye(14))
assert A.row_join(B)*Krat==s.zeros(14,14)
assert Krat.rank()==14
Gn=np.array(G,float);vals,U=np.linalg.eigh(Gn);Qn=U@np.diag(1/np.sqrt(vals))
Pn=np.linalg.solve(Qn,np.array(P,float)@Qn);om=np.exp(2j*np.pi/3)
proj=(np.eye(n)+Pn/om+Pn@Pn/om**2)/3
U1,sv,_=np.linalg.svd(proj);X=Qn@U1[:,:7];Y=X.conj()
assert np.allclose(X.conj().T@Gn@X,np.eye(7))
assert np.allclose(np.array(P,float)@X,om*X)
a=X.T@np.array(slice(h1),float)@Y;b=X.T@np.array(slice(h2),float)@Y
HH=s.Matrix.hstack(h1,h2);GH=HH.T*G*HH
assert GH==s.Matrix([[s.Rational(1526,13471),s.Rational(1616,13471)],[s.Rational(1616,13471),s.Rational(238495303,76582635)]])
M=np.hstack([a/np.sqrt(float(GH[0,0])),b/np.sqrt(float(GH[1,1]))])
_,sv,vh=np.linalg.svd(M,full_matrices=True);K=vh.conj().T[:,7:]
assert np.linalg.norm(M@K)<1e-8
assert np.allclose(K.conj().T@K,np.eye(7))
assert np.allclose(sv,[11.07600673,10.37289271,8.54202158,6.1022267,5.56084364,3.74847715,2.75579797])
he,hu=np.linalg.eigh(np.array(GH,float));wh=hu@np.diag(1/np.sqrt(he))@hu.T
MS=[a,b];Morth=np.hstack([sum(MS[i]*wh[i,j] for i in range(2)) for j in range(2)])
# Joint orthonormalization assumes unit metric on the two block labels;
# this is not the actual selected E32/E33 vacuum with fixed amplitudes.
print('separate normalization',sv)
print('joint Higgs coordinate normalization',np.linalg.svd(Morth,compute_uv=False))
assert np.allclose(K.conj().T@np.eye(14)@K,np.eye(7))
# Further pairing C=[C1 C2] restricts to C2-C1 A^-1 B on rational kernel.
# Actual conjugate-sector map is NOT produced by the holomorphic cubic.
print('PASS actual quotient Gram, two full-rank slices, kernel and universal current')
print('OPEN conjugate pairing, physical CY metric, F/D vacuum and fresh CMS prediction')
