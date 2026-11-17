#!/usr/bin/env python3
"""P1d GaAs(111) coherent biaxial-film physics and 8-band consistency.
Source: Vurgaftman et al. DOI 10.1063/1.1368156;
strained QW DOI 10.1103/PhysRevB.84.195207;
Bahder + erratum DOIs 10.1103/PhysRevB.41.11992, .46.9913.
Not FULL Bahder: strain-dependent conduction shear b', spin-orbit strain,
and independent strain-k momentum coefficients remain uncalibrated.
Not a self-assembled QD/PL, EQE, or PV maximum-power measurement.
"""
import argparse, json
from pathlib import Path
import numpy as np
from check_gaas_111_kane_birpikus_maxcut import (
    C3_AXIS, EP_EV, EG_300K_EV, REMOTE_F_0K, A_C_EV,
    axis_tensor, hso_valence, bir_pikus_xyz, transition_spectrum)
C11,C12,C44=118.8,53.8,59.4
G1,G2,G3=6.98,2.06,2.93
E14=-0.16
EPS0=8.8541878128e-12; EPSR=12.9

def pseudomorphic_111(in_plane,c11=C11,c12=C12,c44=C44):
    denominator=c11+2*c12+4*c44
    if min(c11-c12,c44,denominator)<=0:raise ValueError("unstable elastic coefficients")
    ratio=-2*(c11+2*c12-2*c44)/denominator
    out_plane=ratio*in_plane
    return axis_tensor(C3_AXIS,out_plane,in_plane),out_plane,ratio

def cubic_stress(e):
    tr=np.trace(e)
    return (C12*tr*np.eye(3)+(C11-C12)*np.diag(np.diag(e))
            +2*C44*(e-np.diag(np.diag(e))))

def piezo_port(e):
    # Tensor, NOT Voigt strain: P = 2 e14 (eps_yz,eps_xz,eps_xy).
    P=2*E14*np.array((e[1,2],e[0,2],e[0,1]))
    P111=float(C3_AXIS@P)
    # Only the unscreened homogeneous planar-interface capacitor limit.
    return P111,-P111/(EPS0*EPSR)

def modified_gamma(eg=EG_300K_EV):
    # Conduction is explicitly present; six-band gamma must be corrected.
    return (G1-EP_EV/(3*eg),G2-EP_EV/(6*eg),G3-EP_EV/(6*eg))

def lk_valence(k,subtract_conduction=True):
    g1,g2,g3=modified_gamma() if subtract_conduction else (G1,G2,G3)
    k=np.asarray(k,float);kin=float(k@k)
    xyz=-((g1-2*g2)*kin*np.eye(3)+6*g2*np.diag(k*k)
          +6*g3*(np.outer(k,k)-np.diag(k*k)))
    return np.kron(xyz,np.eye(2))

def eight_state(k,e,geometry_strain_k=False,subtract_conduction=True):
    k=np.asarray(k,float)
    kp=(np.eye(3)-e)@k if geometry_strain_k else k
    # geometry_strain_k is a KINEMATIC test, not Bahder's complete k*strain.
    val=hso_valence()+np.kron(bir_pikus_xyz(e),np.eye(2))+lk_valence(k,subtract_conduction)
    ec=EG_300K_EV+A_C_EV*np.trace(e)+(1+2*REMOTE_F_0K)*float(k@k)
    b=np.zeros((2,6),complex)
    for j in range(3):
        for spin in range(2): b[spin,2*j+spin]=np.sqrt(EP_EV)*kp[j]
    return np.block([[ec*np.eye(2),b],[b.conj().T,val]])

def verify():
    tests=[]
    def test(label,ok):
        assert bool(ok),label
        tests.append(label)
    z=np.zeros((3,3))
    test("reduced exact GaAs ratio",abs(pseudomorphic_111(1)[2]+269/580)<1e-14)
    test("111 effective Poisson convention",abs((269/580)/(2+269/580)-.18824352694191743)<1e-13)
    for f in (-.01,-.005,-.002,0,.002,.005,.01):
        e,out,r=pseudomorphic_111(f)
        sigma=cubic_stress(e)
        test(f"{f} zero normal traction",abs(C3_AXIS@sigma@C3_AXIS)<1e-12)
        test(f"{f} zero transverse traction",np.linalg.norm(
            (np.eye(3)-np.outer(C3_AXIS,C3_AXIS))@sigma@C3_AXIS)<1e-12)
        test(f"{f} in-plane tensor",np.allclose(e@C3_AXIS,out*C3_AXIS,atol=1e-14))
        test(f"{f} trace",np.isclose(np.trace(e),out+2*f))
        P,E=piezo_port(e)
        test(f"{f} piezo tensor identity",abs(P-2*E14*(out-f)/np.sqrt(3))<1e-15)
        test(f"{f} finite interface potential",np.isfinite(E))
        test(f"{f} Hermitian Kane",np.allclose(eight_state([0,0,0],e),eight_state([0,0,0],e).conj().T))
        lines=transition_spectrum(e)
        test(f"{f} complete Kane oscillator sum",all(
            abs(sum(l["strength_ep_units"][name] for l in lines)-2)<1e-11
            for name in ("longitudinal111","transverseA","transverseB")))
    test("unstrained piezo zero",abs(piezo_port(z)[0])<1e-18)
    test("001 axial piezo zero",abs(piezo_port(axis_tensor([0,0,1],.005))[0])<1e-18)
    test("field sign reverses",np.isclose(piezo_port(pseudomorphic_111(.005)[0])[1],
                                    -piezo_port(pseudomorphic_111(-.005)[0])[1]))
    test("kinematic strain k zero fixture",np.allclose(eight_state([.03,.01,.02],z),
                                                 eight_state([.03,.01,.02],z,True)))
    test("kinematic strain k is not zero",not np.allclose(eight_state([.03,.01,.02],pseudomorphic_111(.005)[0]),
                                                         eight_state([.03,.01,.02],pseudomorphic_111(.005)[0],True)))
    test("gamma 8-band reparameterization finite",np.all(np.isfinite(modified_gamma())))
    for name,axis,gamma in (("001",[0,0,1],G2),("111",C3_AXIS,G3)):
        small=1e-7
        k=np.asarray(axis,float)/np.linalg.norm(axis)*np.sqrt(small)
        zero=np.linalg.eigvalsh(eight_state([0,0,0],z))
        eig=np.linalg.eigvalsh(eight_state(k,z))
        test(f"{name} HH LH curvature from 8-band renorm",
             np.allclose((eig[2:6]-zero[2:6])/small,
                         np.repeat((-G1-2*gamma,-G1+2*gamma),2),atol=5e-4))
        test(f"{name} conduction mass curvature",
             np.allclose((eig[6:]-zero[6:])/small,1/.062237926,atol=4e-4))
        test(f"{name} spin Kramers pairs",
             max(abs(eig[2]-eig[3]),abs(eig[4]-eig[5]))<1e-10)
        bad=np.linalg.eigvalsh(eight_state(k,z,False,False))
        test(f"{name} raw six-band gamma double counts Kane",
             np.linalg.norm(bad[2:6]-eig[2:6])>1e-7)
    return tests

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    checks=verify()
    e,out,r=pseudomorphic_111(.005)
    receipt={
        "passed":len(checks),"all_passed":True,"checks":checks,
        "GaAs_300K_fixture":{"C11_GPa":C11,"C12_GPa":C12,"C44_GPa":C44,
            "epsilon_parallel":.005,"epsilon_normal":out,"normal_ratio":r,
            "delta":out-.005,"trace":float(np.trace(e)),
            "P_111_C_m2":piezo_port(e)[0],
            "UNSCREENED_field_V_m":piezo_port(e)[1],
            "conditional_5nm_V":piezo_port(e)[1]*5e-9,
            "eightband_gamma_prime":modified_gamma(),
            "polarized_edges":transition_spectrum(e)},
        "open":["nonuniform QD strain","full Bahder a-prime/b-prime shear and spin-orbit strain",
                "full strain*k couplings","measured exciton/HH/LH spectra",
                "absorption coefficients & carrier collection","AM1.5G terminal JV",
                "369 predictive advantage beyond group theory"]}
    if args.output:args.output.write_text(json.dumps(receipt,indent=2)+"\n")
    print(json.dumps({"passed":len(checks),"GaAs_300K_fixture":receipt["GaAs_300K_fixture"]},indent=2))
if __name__=="__main__":main()
