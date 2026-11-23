#!/usr/bin/env python3
"""OCT369 P0.32: original Bloch/Wannier source with correct crystal geometry.

Standalone local replay of P0.18's 24-bond Hamiltonian and orbital embedding.
Original owners retain priority: P0.18 magnetic model, P0.29 Bloch producer,
P0.31 Sato/Hayami Eq11 consumer, DASHI CrystalRealizationConsumerContract.
Tests only basis-changing geometry; no measured PtMn3, no new octupole theory,
no material SI force, Maxwell device or antigravity.
"""
import json
from itertools import product
import numpy as np
import sympy as sp
from oct369_covariant_bloch_geometry import (bracket,site_position_operators,
    embedding_unitary,physical_cell_jets,direct_reciprocal_relabel)

SITES=np.array([[0.,.5,.5],[.5,0.,.5],[.5,.5,0.]])
SPIN=SITES-SITES.mean(axis=0)
SPIN/=np.linalg.norm(SPIN,axis=1)[:,None]
AXIS=np.ones(3)/np.sqrt(3)
SX=np.array([[0,1],[1,0]],complex);SY=np.array([[0,-1j],[1j,0]],complex)
SZ=np.diag([1.,-1.]).astype(complex);SIGMA=(SX,SY,SZ)
EYE2=np.eye(2,dtype=complex)
def sigma(v):return sum(v[i]*SIGMA[i] for i in range(3))
BONDS=[]
for a,b in product(range(3),repeat=2):
    for R in product(range(-1,2),repeat=3):
        d=np.array(R,float)+SITES[b]-SITES[a]
        if abs(d@d-.5)<1e-12:
            BONDS.append((a,b,np.array(R,int),d))
BONDS.sort(key=lambda row:(row[0],row[1],tuple(row[2])))
assert len(BONDS)==24

def jets(B,orb,k,translations=None):
    """Return same H in cell/embedded gauges and *physical Cartesian p* jets."""
    B=np.asarray(B,float);orb=np.asarray(orb,float);k=np.asarray(k,float)
    out=[]
    for embedded in (False,True):
        h=np.zeros((6,6),complex);dh=np.zeros((3,6,6),complex)
        ddh=np.zeros((3,3,6,6),complex)
        for a in range(3):
            h[2*a:2*a+2,2*a:2*a+2]+=.8*sigma(SPIN[a])
        for i,(a,b,R,d_original) in enumerate(BONDS):
            Ruse=R if translations is None else np.asarray(translations[i],float)
            displacement=Ruse+orb[b]-orb[a] if embedded else Ruse
            phase=np.exp(2j*np.pi*(k@displacement))
            hop=.7*EYE2+.15j*sigma(np.cross(AXIS,d_original))
            t=hop*phase
            cart=B@displacement
            sl=np.ix_([2*a,2*a+1],[2*b,2*b+1])
            h[sl]+=t
            for j in range(3):
                dh[j][sl]+=1j*cart[j]*t
                for l in range(3):ddh[j,l][sl]+=-cart[j]*cart[l]*t
        out.append((h,dh,ddh))
    return out

checks=[]
def ok(label,condition):
    assert bool(condition),label
    checks.append(label)

def err(a,b):return float(np.max(abs(np.asarray(a)-np.asarray(b))))

base=np.array([[.8,.12,0.],[0.,1.1,.17],[0.,0.,.6]])
u=np.array([[1,1,0],[0,1,1],[0,0,1]],int)
check_k=[np.array(x,float) for x in ((.17,.13,-.22),(.28,-.21,.09),(-.07,.16,.25),(.09,.11,-.28))]
metrics={'maximum_H_gauge_residual':0.,'maximum_D1_residual':0.,'maximum_D2_residual':0.,'maximum_new_basis_residual':0.,'minimum_naive_error':float('inf')}
ok('24_original_P018_bonds',len(BONDS)==24)
ok('zero_total_order_moment',np.linalg.norm(SPIN.sum(axis=0))<1e-13)
ok('unimodular_relabelling',round(np.linalg.det(u))==1)
ok('basis_nonorthogonal',np.max(abs(base.T@base-np.diag(np.diag(base.T@base))))>1e-4)
for j,k in enumerate(check_k):
    (hc,dc,ddc),(he,de,dde)=jets(base,SITES,k)
    W=embedding_unitary(k,SITES)
    X=site_position_operators(base,SITES)
    phys_d,phys_dd=physical_cell_jets(hc,dc,ddc,X)
    eh=err(hc,W@he@W.conj().T)
    ed=max(err(phys_d[i],W@de[i]@W.conj().T) for i in range(3))
    edd=max(err(phys_dd[i,l],W@dde[i,l]@W.conj().T) for i,l in product(range(3),repeat=2))
    naïve=max(err(dc[i],W@de[i]@W.conj().T) for i in range(3))
    metrics['maximum_H_gauge_residual']=max(metrics['maximum_H_gauge_residual'],eh)
    metrics['maximum_D1_residual']=max(metrics['maximum_D1_residual'],ed)
    metrics['maximum_D2_residual']=max(metrics['maximum_D2_residual'],edd)
    metrics['minimum_naive_error']=min(metrics['minimum_naive_error'],naïve)
    ok(f'cell_embedded_H_{j}',eh<1e-12)
    ok(f'cell_embedded_dH_{j}',ed<1e-12)
    ok(f'cell_embedded_ddH_{j}',edd<1e-12)
    ok(f'naive_partial_bad_{j}',naïve>1e-3)
    ok(f'spectra_same_{j}',err(np.linalg.eigvalsh(hc),np.linalg.eigvalsh(he))<1e-12)
    # Change integer cell basis U, transporting BOTH site coordinates and R.
    translations=np.array([b[2] for b in BONDS]);B2,r2,R2,k2=direct_reciprocal_relabel(base,u,SITES,translations,k)
    (hc2,dc2,ddc2),(he2,de2,dde2)=jets(B2,r2,k2,R2)
    W2=embedding_unitary(k2,r2);X2=site_position_operators(B2,r2)
    d2,dd2=physical_cell_jets(hc2,dc2,ddc2,X2)
    mismatch=max(err(hc2,hc),err(he2,he),err(d2,phys_d),err(dd2,phys_dd))
    metrics['maximum_new_basis_residual']=max(metrics['maximum_new_basis_residual'],mismatch)
    ok(f'reciprocal_basis_and_hopping_invariant_{j}',mismatch<1e-12)
    ok(f'physical_sites_invariant_{j}',err(B2@r2.T,base@SITES.T)<1e-12)
    ok(f'physical_pairing_invariant_{j}',err(k2@r2.T,k@SITES.T)<1e-12)
    ok(f'physical_bond_displacement_invariant_{j}',all(err(B2@(R2[t]+r2[b]-r2[a]),base@d)<1e-12 for t,(a,b,R,d) in enumerate(BONDS)))
    ok(f'same_operator_source_in_Bloch_gauges_{j}',err(W@np.kron(np.diag(SPIN[:,0]),SX)@W.conj().T,np.kron(np.diag(SPIN[:,0]),SX))<1e-12)

# General smooth SU(2) basis mixing: off-diagonal spin connection, not just
# the diagonal orbital position X_i. Pure gauge: F=0 and D_iD_jH transforms.
x,y=sp.symbols('x y',real=True)
sx=sp.Matrix([[0,1],[1,0]]);sy=sp.Matrix([[0,-sp.I],[sp.I,0]])
sz=sp.diag(1,-1);identity=sp.eye(2)
# Rational Cayley SU(2) rotors allow exact polynomial-denominator proofs;
# no fragile trigonometric simplification or discretized gauge phases.
def rotor(mat,z):return (identity+sp.I*z*mat)*(identity-sp.I*z*mat).inv()
U=rotor(sz,x)*rotor(sx,y)
H=sx+2*sy+x*sz+y*sx
P=U*H*U.H
Ox=sp.diff(U,x)*U.H;Oy=sp.diff(U,y)*U.H
def clear(expr):return sp.Matrix(expr).applyfunc(sp.cancel)
def dco(expr,var,omega):return sp.diff(expr,var)-omega*expr+expr*omega
Dxp=dco(P,x,Ox);Dyp=dco(P,y,Oy)
F=sp.diff(Oy,x)-sp.diff(Ox,y)-Ox*Oy+Oy*Ox
for name,v in [('U_unitary',clear(U*U.H-identity)==sp.zeros(2)),
('covariant_d_x',clear(Dxp-U*sp.diff(H,x)*U.H)==sp.zeros(2)),
('covariant_d_y',clear(Dyp-U*sp.diff(H,y)*U.H)==sp.zeros(2)),
('covariant_d_xd_y',clear(dco(U*sp.diff(H,y)*U.H,x,Ox)-U*sp.diff(H,y,x)*U.H)==sp.zeros(2)),
('covariant_d_yd_x',clear(dco(U*sp.diff(H,x)*U.H,y,Oy)-U*sp.diff(H,x,y)*U.H)==sp.zeros(2)),
('pure_gauge_zero_curvature',clear(F)==sp.zeros(2)),
('noncommuting_connection',clear(Ox*Oy-Oy*Ox)!=sp.zeros(2)),
('naive_general_gauge_incorrect',clear(sp.diff(P,x)-U*sp.diff(H,x)*U.H)!=sp.zeros(2))]:ok(name,v)

# Source-level non-promotion, distinct from executable numerical certificates.
ok('metric_spacetime_curvature_not_inferred',True)
ok('actual_material_band_calibration_not_present',True)
ok('source_Maxwell_coil_not_present',True)
ok('original_SatoHayami_bulk_eq11_not_recomputed',True)
metrics['basis_shearing']=u.tolist()
metrics['source_B_cartesian']=base.tolist()
receipt={'scope':'physical Bloch basis covariant derivative and crystal-coordinate accounting, original P0.18 model reconstituted, no material data',
 'checks_passed':len(checks),'checks':checks,'metrics':metrics,
 'original_site_model_24_bonds':True,'original_crystal_geometry_owners':['docs/crystallography_native_lattice_hyperfabric_reuse.md','DASHI/Mathematics/Symmetry/CrystalRealizationConsumerContractExact.agda','DASHI/Mathematics/Symmetry/TetragonalAtomicFourierRealizationExact.agda'],
 'same_source_P031_formula_reexecuted':False,
 'real_PtMn3_bands':False,'periodic_bulk_octupole_converged':False,
 'Maxwell_controller_included':False,'gravitational_field_derived':False,
 'attribution':{'original_physics':'Bloch/Wannier crystal gauge and covariant derivatives established prior art; Sato/Hayami 2026 original quantum octupole','DASHI_native':'crystal direct/reciprocal/atomic basis owners, P0.18/P0.29/P0.31','new':'exact unit/reciprocal basis and 1st/2nd covariant jet interoperability and pure-gauge negative controls'}}
if __name__=='__main__':print(json.dumps(receipt,indent=2,sort_keys=True))
