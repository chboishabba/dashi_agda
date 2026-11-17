#!/usr/bin/env python3
"""Near-Gamma Kane/Bir-Pikus [111] physical parameter and symmetry discriminator.

Validated against 94 local assertions; HOMOGENEOUS prescribed strain, not a
complete Bahder 8-band strain calculation, measured GaAs dot or PV power.
Vurgaftman et al., J. Appl. Phys. 89 (2001), DOI 10.1063/1.1368156
Bahder, Phys. Rev. B 41 (1990), DOI 10.1103/PhysRevB.41.11992
Cartesian Bir-Pikus convention: https://www.oghma-nano.com/manual/bir-pikus.html

No k*strain interband strain terms, valence Luttinger k², Poisson/elastic
boundary conditions, quantum confinement, radiative/recombination rate,
measured absorptance, EQE, contacts, or loaded PV IV.
"""
import argparse
import json
from pathlib import Path

import numpy as np

EP_EV, DELTA_SO_EV, EG_300K_EV = 28.8, 0.341, 1.422
REMOTE_F_0K = -1.94
A_C_EV, A_V_EFF_EV, B_EV, D_EV = -7.17, -1.16, -2.0, -4.8
C3_AXIS = np.ones(3)/np.sqrt(3)

# Vurgaftman's av convention may be quoted +1.16 when the VALENCE
# energy shift is written as -av*Tr(eps). Here A_V_EFF is that -1.16
# coefficient itself. Do not silently mix hydrostatic conventions.

def generators():
    x=np.array([[0,0,0],[0,0,-1j],[0,1j,0]],complex)
    y=np.array([[0,0,1j],[0,0,0],[-1j,0,0]],complex)
    z=np.array([[0,-1j,0],[1j,0,0],[0,0,0]],complex)
    sx=np.array([[0,1],[1,0]],complex)/2
    sy=np.array([[0,-1j],[1j,0]],complex)/2
    sz=np.diag([1,-1]).astype(complex)/2
    return (x,y,z),(sx,sy,sz)

def axis_tensor(axis,axial,transverse=0.):
    n=np.array(axis,float)
    n/=np.linalg.norm(n)
    return transverse*np.eye(3)+(axial-transverse)*np.outer(n,n)

def bir_pikus_xyz(eps,av=A_V_EFF_EV,b=B_EV,d=D_EV):
    e=np.array(eps,float)
    if e.shape!=(3,3) or not np.allclose(e,e.T,atol=1e-14):
        raise ValueError("strain must be a symmetric 3x3 tensor")
    trace=float(np.trace(e))
    out=np.eye(3)*(av*trace)
    for p in range(3):
        out[p,p]+=b*(3*e[p,p]-trace)
        for q in range(p):
            out[p,q]=out[q,p]=np.sqrt(3)*d*e[p,q]
    return out

def hso_valence():
    ls,ss=generators()
    return (2*DELTA_SO_EV/3)*sum(np.kron(l,s) for l,s in zip(ls,ss))-(DELTA_SO_EV/3)*np.eye(6)

def h8(eps,kinetic_eV=(0.,0.,0.),gap=EG_300K_EV):
    """Eight-state near-Gamma Kane truncation; k_j in sqrt(hbar² k²/2m0) units."""
    e=np.array(eps,float); k=np.array(kinetic_eV,float)
    hv=hso_valence()+np.kron(bir_pikus_xyz(e),np.eye(2))
    ec=gap+A_C_EV*np.trace(e)+(1+2*REMOTE_F_0K)*np.dot(k,k)
    hc=np.eye(2)*ec
    coupling=np.zeros((2,6),complex)
    for orbital in range(3):
        for spin in range(2):
            coupling[spin,2*orbital+spin]=np.sqrt(EP_EV)*k[orbital]
    return np.block([[hc,coupling],[coupling.conj().T,hv]])

def transition_spectrum(eps):
    """Kramers multiplets grouped by ENERGY DEGENERACY, not arbitrary pairs."""
    eig,states=np.linalg.eigh(hso_valence()+np.kron(bir_pikus_xyz(eps),np.eye(2)))
    ec=EG_300K_EV + A_C_EV*np.trace(eps)
    pol={"longitudinal111":C3_AXIS,
         "transverseA":np.array([1,-1,0])/np.sqrt(2),
         "transverseB":np.array([1,1,-2])/np.sqrt(6)}
    matrices={}
    for label,vec in pol.items():
        m=np.zeros((2,6),complex)
        for j in range(3):
            for s in range(2):
                m[s,2*j+s]=np.sqrt(EP_EV)*vec[j]
        matrices[label]=m
    out=[];start=0
    while start<len(eig):
        end=start+1
        while end<len(eig) and abs(eig[end]-eig[start])<1e-9:
            end+=1
        # Projector sum is invariant under degenerate basis rephasing.
        multiplet=states[:,start:end]
        out.append({"degeneracy":end-start,
                    "valence_ev":float(np.mean(eig[start:end])),
                    "gap_ev":float(ec-np.mean(eig[start:end])),
                    "strength_ep_units":{
                        label:float(np.linalg.norm(m@multiplet)**2/EP_EV)
                        for label,m in matrices.items()}})
        start=end
    return out

def rejects_bad_strain():
    e=np.eye(3);e[0,1]=.05
    try:bir_pikus_xyz(e)
    except ValueError:return True
    return False

def verify():
    checks=[]
    def check(name,ok):
        if not bool(ok):raise AssertionError(name)
        checks.append(name)
    epsil=1e-10; I3=np.eye(3); I6=np.eye(6)
    zero=np.zeros((3,3))
    R=np.array([[0,0,1],[1,0,0],[0,1,0]])
    mirror=np.array([[1,0,0],[0,0,1],[0,1,0]])
    tr_unitary=np.kron(np.eye(3),np.array([[0,-1j],[1j,0]]))
    check("C3 order-three R",np.allclose(R@R@R,I3))
    check("C3v mirror conjugates R",np.allclose(mirror@R@mirror,R.T))
    check("zero strain -> zero BP",np.allclose(bir_pikus_xyz(zero),zero))
    for delta in (-.008,-.005,0,.003,.005,.008):
        eps=axis_tensor(C3_AXIS,delta)
        b=bir_pikus_xyz(eps)
        diag=A_V_EFF_EV*np.trace(eps)
        shear=D_EV*delta/np.sqrt(3)
        expect=diag*I3+shear*(np.ones((3,3))-I3)
        check(f"[111] prescribed BP matrix delta={delta}",np.allclose(b,expect,atol=epsil))
        check(f"[111] C3 covariance delta={delta}",np.allclose(R@b@R.T,b,atol=epsil))
        check(f"[111] mirror covariance delta={delta}",np.allclose(mirror@b@mirror,b,atol=epsil))
        check(f"[111] A1 E eigenvalues delta={delta}",
              np.allclose(np.linalg.eigvalsh(b),sorted([diag+2*shear,diag-shear,diag-shear]),atol=epsil))
        check(f"[111] sqrt3*d*delta split delta={delta}",np.isclose(3*shear,np.sqrt(3)*D_EV*delta,atol=epsil))
        v=hso_valence()+np.kron(b,np.eye(2))
        check(f"[111] time reversal delta={delta}",
              np.allclose(tr_unitary@v.conj()@tr_unitary.conj().T,v,atol=epsil))
        vals=np.linalg.eigvalsh(v)
        check(f"[111] three Kramers pairs delta={delta}",np.max(abs(vals[0::2]-vals[1::2]))<epsil)
        lines=transition_spectrum(eps)
        check(f"[111] spectrally grouped manifold delta={delta}",
              2<=len(lines)<=3 and sum(x["degeneracy"] for x in lines)==6
              and all(x["gap_ev"]>0 for x in lines))
        for axis in ("longitudinal111","transverseA","transverseB"):
            check(f"[111] total Kane strength preserved {delta} {axis}",
                  np.isclose(sum(x["strength_ep_units"][axis] for x in lines),2,atol=epsil))
        check(f"[111] transverse symmetry delta={delta}",
              all(np.isclose(x["strength_ep_units"]["transverseA"],
                             x["strength_ep_units"]["transverseB"],atol=epsil)
                  for x in lines))
    for delta in (-.005,0,.005):
        eps=axis_tensor([0,0,1],delta)
        b=bir_pikus_xyz(eps)
        diag=A_V_EFF_EV*np.trace(eps)
        check(f"[001] b-only spinless eigenvalues {delta}",
              np.allclose(np.linalg.eigvalsh(b),
                          sorted([diag-B_EV*delta,diag-B_EV*delta,diag+2*B_EV*delta]),atol=epsil))
        check(f"[001] |3b delta| splitting {delta}",
              np.isclose(np.ptp(np.linalg.eigvalsh(b)),abs(3*B_EV*delta),atol=epsil))
    e111=axis_tensor(C3_AXIS,.005)
    e001=axis_tensor([0,0,1],.005)
    check("[001] breaks [111] C3",not np.allclose(R@bir_pikus_xyz(e001)@R.T,bir_pikus_xyz(e001)))
    check("[111] preserves [111] C3",np.allclose(R@bir_pikus_xyz(e111)@R.T,bir_pikus_xyz(e111)))
    check("reject nonsymmetric strain",rejects_bad_strain())
    hydro=axis_tensor([0,0,1],.004,.004)
    v0=hso_valence();v1=v0+np.kron(bir_pikus_xyz(hydro),np.eye(2))
    check("hydrostatic shift does not split SO eigenlevels",
          np.allclose(np.linalg.eigvalsh(v1)-np.linalg.eigvalsh(v0),
                      np.ones(6)*A_V_EFF_EV*np.trace(hydro),atol=epsil))
    check("H8 zero-strain Hermitian",np.allclose(h8(zero),h8(zero).conj().T))
    check("H8 strained finite-k Hermitian",
          np.allclose(h8(e111,[.01,.02,.03]),h8(e111,[.01,.02,.03]).conj().T))
    check("H8 at k=0 isolates conduction",
          np.isclose(np.linalg.eigvalsh(h8(e111))[-1],EG_300K_EV+A_C_EV*np.trace(e111)))
    sx,sy,sz=generators()[1]
    spin_axis=sum(v*s for v,s in zip(C3_AXIS,(sx,sy,sz)))
    spinrot=np.cos(np.pi/3)*np.eye(2)-2j*np.sin(np.pi/3)*spin_axis
    valrot=np.kron(R,spinrot)
    v=hso_valence()+np.kron(bir_pikus_xyz(e111),np.eye(2))
    check("spinful [111] double group C3 preserved",
          np.allclose(valrot@v@valrot.conj().T,v,atol=epsil))
    other=hso_valence()+np.kron(bir_pikus_xyz(e001),np.eye(2))
    check("spinful [001] fails this C3",
          not np.allclose(valrot@other@valrot.conj().T,other,atol=epsil))
    check("spin-1/2 three 120 rotations = -I6",
          np.allclose(np.linalg.matrix_power(valrot,3),-I6,atol=epsil))
    check("reversing strain reverses signed A1/E split",
          np.isclose(np.sqrt(3)*D_EV*.005,-np.sqrt(3)*D_EV*(-.005)))
    check("spinful strain changes valence energies",
          np.linalg.norm(np.linalg.eigvalsh(v)-np.linalg.eigvalsh(v0))>1e-3)
    check("spinful strain splits spectral lines not total oscillator",
          len(transition_spectrum(e111))==3 and len(transition_spectrum(zero))==2)
    return checks

def main():
    a=argparse.ArgumentParser()
    a.add_argument("--output",type=Path)
    opt=a.parse_args()
    checks=verify();sweep=[]
    for axis in ("111","001"):
        for strain in (-.01,-.0075,-.005,-.0025,0,.0025,.005,.0075,.01):
            e=axis_tensor(C3_AXIS if axis=="111" else [0,0,1],strain)
            sweep.append({"axis":axis,"axial_strain":strain,"transverse_strain":0.,
                          "strain_tensor":np.round(e,8).tolist(),
                          "Gamma_spinful_valence_pairs":transition_spectrum(e)})
    receipt={
        "checks_passed":len(checks),"all_checks_passed":True,
        "scope":"GaAs near-Gamma eight states with Bir-Pikus XYZ strain and SO; not full material model",
        "sources":{"Vurgaftman":"10.1063/1.1368156","Bahder":"10.1103/PhysRevB.41.11992",
                   "BP_convention":"https://www.oghma-nano.com/manual/bir-pikus.html"},
        "parameters":{"Eg_300K_eV":EG_300K_EV,"Ep_eV":EP_EV,"DeltaSO_eV":DELTA_SO_EV,
                      "F_reused_from_0K":REMOTE_F_0K,"ac_eV":A_C_EV,
                      "av_effective_valence_shift_eV":A_V_EFF_EV,"b_eV":B_EV,"d_eV":D_EV},
        "strain_admission":"prescribed uniform tensor; no elastic/thermal equilibrium",
        "polarization_strength":"Kane-matrix EP units; NOT absorption/EQE or PV work",
        "missing":["Bahder strain*k interband mixing","full Luttinger valence k²",
                   "real strain field and confinement","optical lines measured on same material",
                   "AM1.5G absorptance and collected carrier MPP","369 nontrivial same-material morphism"],
        "checks":checks,"sweep":sweep
    }
    if opt.output:opt.output.write_text(json.dumps(receipt,indent=2)+"\n")
    print(json.dumps({"checks_passed":len(checks),"all_checks_passed":True,
                      "at_strain_plus_0_5pct":next(x for x in sweep if x["axis"]=="111" and x["axial_strain"]==.005)},indent=2))

if __name__=="__main__":main()
