#!/usr/bin/env python3
"""M2 strict conventional 4T 3J topology (no invented laboratory I-V).

NREL GaInP/GaAs//Si 2017 mechanical stack:
THREE optical absorbers; TWO independently extracted terminal groups.
GaInP and GaAs are series-connected inside one output, Si separately
contacted. Published Green v68 Table 4 voltage/current/FF pairs describe
electrical GROUPS, never all three optical junctions separately.
Conditional non-multiplication upper bound on a series output Jsc:
I_top <= min(q*integral(photonflux*A_GaInP),
             q*integral(photonflux*A_GaAs)).
Actual top series characteristic and Si IV must be SOURCE MEASURED.
No assumption that measured GaInP/GaAs group EQE equals A_GaInP+A_GaAs.
"""
import json
import numpy as np

Q=1.602176634e-19
H=6.62607015e-34
C=299792458.0
ORDER=("GaInP","GaAs","Si")
GROUPS=(("GaInP","GaAs"),("Si",))

def check_groups(optical_names,groups):
    if tuple(optical_names)!=ORDER or tuple(tuple(group) for group in groups)!=GROUPS:
        raise ValueError("NREL source requires 3 absorber species and exactly 2 electrical groups")
    flattened=[name for group in groups for name in group]
    if len(flattened)!=3 or set(flattened)!=set(ORDER):
        raise ValueError("duplicated or missing absorber")
    return True

def series_current_cap(wavelength_nm,spectral_W_m2_nm,
                       reflectance,absorption,transmission,
                       top_measured_group_Jsc_A_m2,si_measured_group_Jsc_A_m2):
    wl=np.asarray(wavelength_nm,dtype=float)
    power=np.asarray(spectral_W_m2_nm,dtype=float)
    A=np.asarray(absorption,dtype=float)
    R=np.asarray(reflectance,dtype=float)
    T=np.asarray(transmission,dtype=float)
    if (wl.ndim!=1 or len(wl)<3 or A.shape!=(len(wl),3) or
        power.shape!=wl.shape or R.shape!=wl.shape or T.shape!=wl.shape):
        raise ValueError("invalid same-wavelength-grid physical absorber partition")
    if not all(np.isfinite(x).all() for x in (wl,power,A,R,T)):
        raise ValueError("nonfinite irradiance or absorptance")
    if wl[0]<=0 or np.any(np.diff(wl)<=0) or np.min(power)<0:
        raise ValueError("incorrect spectral physical units or wavelength order")
    if np.any(A<0) or np.any(A>1) or np.any(R<0) or np.any(T<0):
        raise ValueError("fractions outside [0,1]")
    if np.any(np.abs(R+A.sum(axis=1)+T-1)>1e-8):
        raise ValueError("double counted or missing incident photons")
    photon_density=power*wl*1e-9/(H*C)
    upper=np.array([Q*np.trapezoid(photon_density*A[:,i],wl) for i in range(3)])
    top=float(top_measured_group_Jsc_A_m2)
    silicon=float(si_measured_group_Jsc_A_m2)
    if not np.isfinite([top,silicon]).all() or min(top,silicon)<0:
        raise ValueError("invalid terminal current densities")
    # One extraction electron per absorbed photon; junctions in series.
    if top>min(upper[0],upper[1])+1e-8 or silicon>upper[2]+1e-8:
        raise ValueError("published 4T grouping contradicts same-source absorption current cap")
    return {"absorber_photon_current_upper_A_m2":upper.tolist(),
       "series_IIIv_group_current_cap_A_m2":float(min(upper[0],upper[1])),
       "source_top_electrical_group_Jsc_A_m2":top,
       "source_separate_Si_group_Jsc_A_m2":silicon,
       "real_source_calibration_authenticated":False,
       "source":"Green 2026 v68 / Essig 2017 35.9% III-V//Si 4T topology",
       "no369_material_gain_claim":True}

def selftest():
    tests=[]
    def ck(n,x):
        assert bool(x),n
        tests.append(n)
    wl=np.linspace(400,1000,41)
    solar=np.ones(len(wl))
    A=np.tile([.25,.25,.3],(len(wl),1))
    R=np.full(len(wl),.1)
    T=np.full(len(wl),.1)
    ck("3 optical absorbers 2 groups",check_groups(ORDER,GROUPS))
    upp=Q*np.trapezoid((solar*wl*1e-9/(H*C))[:,None]*A,wl,axis=0)
    good=series_current_cap(wl,solar,R,A,T,min(upp[:2])*.9,upp[2]*.9)
    ck("top series bound from least current",abs(good["series_IIIv_group_current_cap_A_m2"]-min(upp[:2]))<1e-8)
    ck("Si separate output current",good["source_separate_Si_group_Jsc_A_m2"]>0)
    ck("fixture cannot certify 369",good["no369_material_gain_claim"])
    def reject(f):
        try:f()
        except ValueError:return True
        return False
    ck("reject treating 3J as 3 independent groups",reject(lambda:check_groups(ORDER,(("GaInP",),("GaAs",),("Si",)))))
    ck("reject 4J invented fourth cell",reject(lambda:check_groups((*ORDER,"Ge"),GROUPS)))
    ck("reject missing GaAs",reject(lambda:check_groups(("GaInP","Si"),GROUPS)))
    ck("reject top output over series absorber cap",reject(lambda:series_current_cap(wl,solar,R,A,T,min(upp[:2])*1.05,upp[2]*.9)))
    ck("reject silicon output > absorbed photons",reject(lambda:series_current_cap(wl,solar,R,A,T,min(upp[:2])*.9,upp[2]*1.05)))
    ck("reject lost photons",reject(lambda:series_current_cap(wl,solar,R,A,T*.5,min(upp[:2])*.9,upp[2]*.9)))
    ck("reject duplicated photons",reject(lambda:series_current_cap(wl,solar,R,A*1.1,T,min(upp[:2])*.9,upp[2]*.9)))
    ck("reject swapped wavelength rows",reject(lambda:series_current_cap(wl[::-1],solar,R,A,T,min(upp[:2])*.9,upp[2]*.9)))
    ck("reject negative group output",reject(lambda:series_current_cap(wl,solar,R,A,T,-1,upp[2]*.9)))
    ck("not actual NREL 4T measurement",good["real_source_calibration_authenticated"] is False)
    return {"all_passed":True,"checks_passed":len(tests),
            "synthetic_only":True,"checks":tests,"illustrative":good}

if __name__=="__main__":
    print(json.dumps(selftest(),indent=2))
