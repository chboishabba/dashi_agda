#!/usr/bin/env python3
"""P3/P5 diamond MCG FOV robust-axis allocation and conditional range steelman.

Mathematics, not a calibrated or demonstrated human-heart detector.
Co-located ideal 3-axis channels, independent channel noise, fixed aggregate
sensor-resource budget. Robust over source-moment direction AND a viewing cone.
Does not optimize spatial aperture or the measured noise cross-spectrum.
"""
import argparse
import numpy as np
import sympy as sp

def fov_information(los_fraction, half_angle_degrees, angles=181):
    """Minimum eigenvalue over source orientation and all look directions in cone.

    Rotational axis symmetry reduces azimuth to zero. Fixed trace(W)=1.
    """
    w=np.diag([(1-los_fraction)/2,(1-los_fraction)/2,los_fraction])
    worst=float("inf")
    for th in np.linspace(0,np.deg2rad(half_angle_degrees),angles):
        n=np.array([np.sin(th),0.,np.cos(th)])
        D=3*np.outer(n,n)-np.eye(3)
        eig=np.linalg.eigvalsh(D@w@D)[0]
        worst=min(worst,float(eig))
    return worst

def exact_on_axis():
    z=sp.symbols("z",real=True)
    W=sp.diag((1-z)/2,(1-z)/2,z)
    D=sp.diag(-1,-1,2)
    assert D*W*D==sp.diag((1-z)/2,(1-z)/2,4*z)
    # Equating transverse and axial information gives the E-optimal split.
    assert sp.solve(sp.Eq((1-z)/2,4*z),z)==[sp.Rational(1,9)]
    assert sp.Rational(4,9)/sp.Rational(1,3)==sp.Rational(4,3)
    print("PASS exact known-look axis allocation: x:y:z = 4:4:1")

def fov_scan():
    out=[]
    z_candidates=np.linspace(0,1,1001)
    for angle in [0,10,20,30,45,60,90]:
        vals=np.array([fov_information(z,angle) for z in z_candidates])
        j=int(np.argmax(vals))
        zz=float(z_candidates[j])
        base=fov_information(1/3,angle)
        row={"cone_half_angle_deg":angle,"line_of_sight_fraction":zz,
             "transverse_each_fraction":(1-zz)/2,
             "worst_information":float(vals[j]),
             "equal_axes_information":base,
             "relative_gain":float(vals[j]/base)}
        out.append(row)
        print("FOV",row)
    assert out[0]["relative_gain"]>1.33
    assert abs(out[-1]["line_of_sight_fraction"]-1/3)<0.002
    return out

def time_years(r_m, n, noise_pt_sqrt_hz, a0_pt=50., r0_m=.1,
               threshold=5., coherent_gain=1.):
    """Illustrative coherent known-signal threshold: no trials/no false alarms.

    Noise is spectral amplitude density, interpreted here as effective
    1-second amplitude noise under a chosen Fourier convention. This is an
    idealized normalisation, NOT independently calibrated to the paper.
    """
    amplitude=a0_pt*(r0_m/r_m)**3
    seconds=(threshold*noise_pt_sqrt_hz/
             (amplitude*np.sqrt(n)*coherent_gain))**2
    return seconds/(365.25*86400)

def check_steelman():
    assert abs(time_years(10,1000,7)-15.527163028874)<1e-9
    assert abs(time_years(10,1000,1)-.31688087814)<1e-9
    for r in [10.,100.,1000.]:
        print("RANGE",r,
              "ideal 1000 independent channels 7 pT/sqrt Hz years",
              time_years(r,1000,7.))
    print("PASS coherent threshold scaling; NOT a detection/attribution bound")

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--skip-fov",action="store_true")
    args=p.parse_args()
    exact_on_axis()
    if not args.skip_fov:fov_scan()
    check_steelman()
