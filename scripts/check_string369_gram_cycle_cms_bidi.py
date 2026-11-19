#!/usr/bin/env python3
"""Original source Yukawa, Gram rechart and frozen CMS covariance BIDI.
Atomic radial Gram donor: atomic_radial_identity_repair.py.
No CY wavefunction identification or fresh scattering prediction.
"""
from pathlib import Path
import runpy,json,csv
import numpy as np
R=Path(__file__).resolve().parents[1]
Y=runpy.run_path(str(R/'scripts/check_ckm_from_physical_mass_matrix.py'))['full_yukawa_matrix']()
a=.041240
phase=np.angle((1+2j*np.sqrt(7))/(5+2j))
def cycle(A):return A[0,1]*A[1,2]/(A[0,2]*A[1,1])
assert np.allclose(cycle(Y),7*np.sqrt(3)/(12*a*a)*np.exp(-1j*phase))
D=np.diag([.225**3,.225**2,1])
assert np.allclose(cycle(D@Y@D),cycle(Y))
# Actual original atomic radial producer, not a CY state identification.
atomic=runpy.run_path(str(R/'scripts/atomic_radial_identity_repair.py'))
r,dr=atomic['radial_grid'](80,4000)
_,X=atomic['solve_l_sector'](r,dr,1,0,2)
G=dr*X.T@X
assert np.allclose(G,np.eye(3),atol=1e-10)
# Use the original atomic Gram as a finite test carrier for the original
# Yukawa bilinear. This is a regression, not physical quark radial modes.
def invsqrt(G):
    e,U=np.linalg.eigh(G)
    return (U/np.sqrt(e))@U.conj().T
L=np.diag([a,a*a,a**3])
K=invsqrt(G)
Y0=K@Y@K
Gp=L@G@L
Yp=invsqrt(Gp)@(L@Y@D)@invsqrt(D@G@D)
assert np.allclose(np.linalg.svd(Yp,compute_uv=False),np.linalg.svd(Y0,compute_uv=False))
# Identity gauge current in the physical Gram metric remains identity.
assert np.allclose(invsqrt(Gp)@Gp@invsqrt(Gp),np.eye(3))
j=json.loads((R/'logs/research/w3_frozen_3205d74_t43_comparison_20260513.json').read_text())
p=np.array([b['prediction'] for b in j['perBin']]);d=np.array([b['data'] for b in j['perBin']])
bins=[b['phiStar'] for b in j['perBin']]
path=R/'scripts/data/hepdata/ins2079374_Covariance_phistar_mass_50-76_over_mass_76-106_t44.csv'
# first numeric section is Total uncertainty; later sections must not overwrite
lookup={}
for row in csv.reader(path.read_text().splitlines()):
    try:
        x,y,z=float(row[0]),float(row[3]),float(row[6])
    except (ValueError,IndexError):continue
    lookup.setdefault((x,y),z)
C=np.array([[lookup[x,y] for y in bins] for x in bins])
assert np.allclose(C,C.T)
np.linalg.cholesky(C)
res=p-d
chi=res@np.linalg.solve(C,res)
A=p@np.linalg.solve(C,p);B=p@np.linalg.solve(C,res)
assert abs(chi-38.81734411729611)<1e-8
roots=np.sort(np.roots([A,2*B,chi-72]))
print('cycle',cycle(Y),'atomic Gram error',np.max(abs(G-np.eye(3))))
print('CMS replay',chi,chi/18,'uniform ratio response interval',roots)
print('OPEN physical CY matter Gram, fresh CMS response to physical interaction changes')
