#!/usr/bin/env python3
"""P2: ASTM G173 AM1.5G radiative JV with SOURCE-CONDITIONAL [111] bands.

NOT experimentally fitted GaAs absorptance, a dot device or an independently
certified cell. Uses a deliberately parameterised sqrt(JDOS) onset; the alpha
normalisation, real transitions, collection and angular reciprocity require
new source evidence. No geometric UV/IR recycling or contact losses.
Imports original G173, Kane/Bir-Pikus, and pseudomorphic owners instead of
duplicating them. Original spectral source: NLR ASTM G173-03.
"""
import argparse, json
from pathlib import Path
import numpy as np
from scipy.optimize import minimize_scalar
from check_pv_astm_g173_radiative import load, H, C, KB, Q, T, VT
from check_gaas_111_kane_birpikus_maxcut import (
    hso_valence, bir_pikus_xyz, EG_300K_EV, A_C_EV, EP_EV, axis_tensor, C3_AXIS)
from check_pv_111_pseudomorphic_kane import pseudomorphic_111, C11, C12

def normalized_transverse_directions(n):
    n=np.asarray(n,float);n=n/np.linalg.norm(n)
    helper=np.array([0.,0.,1.]) if abs(n[2])<.9 else np.array([1.,0.,0.])
    a=np.cross(n,helper);a=a/np.linalg.norm(a)
    b=np.cross(n,a)
    return (a,b)

def source_lines(eps,normal):
    """Full spectral-projector weights; never split an exactly degenerate Gamma8."""
    vals,U=np.linalg.eigh(hso_valence()+np.kron(bir_pikus_xyz(eps),np.eye(2)))
    ec=EG_300K_EV+A_C_EV*np.trace(eps)
    output=[];i=0
    while i<6:
        j=i+1
        while j<6 and abs(vals[j]-vals[i])<1e-9:j+=1
        pairs=U[:,i:j]
        strengths=[]
        for light in normalized_transverse_directions(normal):
            m=np.zeros((2,6),complex)
            for orb in range(3):
                for spin in range(2):m[spin,2*orb+spin]=np.sqrt(EP_EV)*light[orb]
            strengths.append(float(np.linalg.norm(m@pairs)**2/EP_EV))
        output.append((float(ec-np.mean(vals[i:j])),sum(strengths)/4))
        i=j
    # Each transverse polarization has two conduction-spin units; the sum
    # over each full valence manifold after two-polarization averaging is 1.
    assert abs(sum(w for _,w in output)-1)<1e-10
    assert all(eg>0 and w>=-1e-12 for eg,w in output)
    return sorted(output)

def absorptance(E,lines,thickness_m,alpha0):
    E=np.asarray(E,float)
    alpha=np.zeros_like(E)
    for eg,w in lines:alpha+=w*np.sqrt(np.maximum(E-eg,0))
    alpha*=alpha0
    return -np.expm1(-alpha*thickness_m)

def radiative_jv(spectrum,lines,thickness_m,alpha0,collection=1):
    """One outgoing emission hemisphere, assumed isotropic A(E), perfect rear mirror.

    Independent collection penalty reduces Jsc only; reciprocity of the
    radiative J0 optical port is retained. NOT a physical recombination model.
    """
    wave=spectrum[:,0];irr=spectrum[:,2]
    solarE=1239.8419843320026/wave
    photon_flux=irr*(wave*1e-9)/(H*C)
    A=absorptance(solarE,lines,thickness_m,alpha0)
    jsc=Q*collection*float(np.trapezoid(photon_flux*A,wave))
    energies=np.linspace(.7,4.5,7601)
    B=2*np.pi*Q**3/(H**3*C**2)
    blackbody_integrand=energies**2*absorptance(energies,lines,thickness_m,alpha0)/np.expm1(energies/VT)
    j0=Q*B*float(np.trapezoid(blackbody_integrand,energies))
    if jsc<=0 or j0<=0:raise ValueError('no physical radiative junction')
    voc=VT*np.log1p(jsc/j0)
    def power(x):return VT*x*(jsc-j0*np.expm1(x))
    opt=minimize_scalar(lambda x:-power(x),bounds=(0,voc/VT),
                        method="bounded",options={"xatol":1e-9})
    return {"Jsc_A_m2":jsc,"J0_A_m2":j0,"Voc_V":voc,
            "Vmp_V":VT*opt.x,"Pmax_W_m2":power(opt.x)}

def run(source,alpha0=4e6):
    global_solar=float(np.trapezoid(source[:,2],source[:,0]))
    assert abs(global_solar-1000.3706555734)<.015
    zero=np.zeros((3,3))
    controls={"unstrained_111":(zero,C3_AXIS)}
    for misfit in (-.005,.005):
        e,_,_=pseudomorphic_111(misfit)
        controls[f"coherent_111_in_plane_{misfit:+.3f}"]=(e,C3_AXIS)
        # The coherent [001] ratio is a different source-specific formula.
        ep_out=-2*C12/C11*misfit
        controls[f"coherent_001_in_plane_{misfit:+.3f}"]=(
            axis_tensor([0,0,1],ep_out,misfit),np.array([0.,0.,1.]))
    outputs={}
    for thickness in (.2e-6,2e-6,20e-6):
        results={}
        for name,(eps,n) in controls.items():
            lines=source_lines(eps,n)
            obj=radiative_jv(source,lines,thickness,alpha0)
            obj["radiative_model_pce_pct"]=100*obj["Pmax_W_m2"]/global_solar
            obj["transverse_lines_eV_weights"]=lines
            results[name]=obj
        base=results["unstrained_111"]["Pmax_W_m2"]
        for name,(eps,n) in controls.items():
            results[name]["delta_from_unstrained_W_m2"]=results[name]["Pmax_W_m2"]-base
        outputs[f"{thickness*1e6:g}_micron"]=results
    # Return explicit same-sample objective and negative control: even a
    # small collection penalty can erase gross optical spectral gains.
    d=2e-6
    e,_,_=pseudomorphic_111(.005)
    lines=source_lines(e,C3_AXIS)
    base=radiative_jv(source,source_lines(zero,C3_AXIS),d,alpha0)["Pmax_W_m2"]
    a,b=0.,1.
    for i in range(65):
        m=(a+b)/2
        if radiative_jv(source,lines,d,alpha0,m)["Pmax_W_m2"]<base:a=m
        else:b=m
    return {"G173_source_global_W_m2":global_solar,
        "assumptions":{"alpha0_m_inverse_sqrt_eV":alpha0,
            "thicknesses_micron":[.2,2,20],
            "emission":"one hemisphere, same A(E) angle-independent hypothetical",
            "collection":"1 ideal except explicit adversarial test",
            "alpha":"weighted sqrt(E-Eg) from gamma-point Kane transitions; NOT measured/fitted"},
        "scenarios":outputs,
        "at_2_micron_111_tensile_collection_break_even_fraction":(a+b)/2,
        "original_spectrum":"NLR ASTM G173-03, 2002 point four-column reference",
        "no_experimental_pce_claim":True}

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--spectrum",required=True)
    p.add_argument("--alpha0",type=float,default=4e6)
    p.add_argument("--output",type=Path)
    x=p.parse_args()
    source=load(x.spectrum)
    r=run(source,x.alpha0)
    if x.output:x.output.write_text(json.dumps(r,indent=2)+"\n")
    print(json.dumps({"global_W_m2":r["G173_source_global_W_m2"],
                      "pce_cases_2_micron":{name:round(o["radiative_model_pce_pct"],5)
                       for name,o in r["scenarios"]["2_micron"].items()},
                      "break_even_collection":r["at_2_micron_111_tensile_collection_break_even_fraction"]},indent=2))
if __name__=="__main__":main()
