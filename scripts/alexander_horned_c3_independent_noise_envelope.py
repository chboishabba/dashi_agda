#!/usr/bin/env python3
"""Analytic mean signal for independent isotropic Gaussian SU(2) gate errors.

For each prescribed ideal gate G_j insert N_j G_j, where
N_j = cos(theta_j/2) + axis_j sin(theta_j/2),
axis_j uniform on S^2 and theta_j ~ N(0,sigma^2) independently.
Then E[N_j] = exp(-sigma^2/8) I. By matrix independence,
E[N_1 G_1 ... N_L G_L] = exp(-L sigma^2/8) G_1 ... G_L.
For the horned-C3 selected root cube, G_1 ... G_L = -I and
L=3*4**depth. The expected normalized Wilson trace is therefore
-exp(-L sigma^2/8). Correlated/coherent/calibration drift invalidates
this model; it is not a hardware performance guarantee.
"""
import argparse
import json
import math
import random


def expected_halftrace(depth, sigma_degrees):
    if depth < 0 or sigma_degrees < 0 or not math.isfinite(sigma_degrees):
        raise ValueError("depth >= 0 and finite sigma_degrees >= 0 required")
    return -math.exp(-3 * 4 ** depth * math.radians(sigma_degrees) ** 2 / 8)


def max_sigma_degrees(depth, min_abs_mean):
    if depth < 0 or not 0 < min_abs_mean <= 1:
        raise ValueError("depth >= 0 and 0 < target <= 1 required")
    return math.degrees(math.sqrt(-8 * math.log(min_abs_mean) / (3 * 4 ** depth)))


def quaternion_product(a, b):
    w,x,y,z=a
    W,X,Y,Z=b
    return (w*W-x*X-y*Y-z*Z, w*X+x*W+y*Z-z*Y,
            w*Y-x*Z+y*W+z*X, w*Z+x*Y-y*X+z*W)


def isotropic_error(rng, sigma):
    a,b,c=(rng.gauss(0, 1) for _ in range(3))
    n=math.sqrt(a*a+b*b+c*c)
    t=rng.gauss(0, sigma)/2
    return (math.cos(t), math.sin(t)*a/n, math.sin(t)*b/n, math.sin(t)*c/n)


def audit(seed=1244, trials=6000, sigma_degrees=4):
    """Monte Carlo independent check using a fixed central -I ideal product.

    Isotropic independent errors make the mean independent of where ideal
    gates occur; one -I gate and remaining identity gates suffice here.
    """
    rng=random.Random(seed)
    sigma=math.radians(sigma_degrees)
    records=[]
    for depth in range(4):
        L=3*4**depth
        readings=[]
        for _ in range(trials):
            p=(-1.,0.,0.,0.)
            for _ in range(L):
                p=quaternion_product(p,isotropic_error(rng,sigma))
            readings.append(p[0])
        measured=sum(readings)/trials
        predicted=expected_halftrace(depth,sigma_degrees)
        # Hoeffding two-sided 99.9% bound for readings in [-1,1].
        radius=math.sqrt(2*math.log(2000)/trials)
        assert abs(measured-predicted)<radius, (depth,measured,predicted)
        records.append(dict(depth=depth,gates=L,predicted=predicted,
                            monte_carlo=measured,conservative_radius=radius))
    for d in range(6):
        assert abs(expected_halftrace(d,max_sigma_degrees(d,0.9))+0.9)<1e-12
        assert math.isclose(max_sigma_degrees(d+1,0.9),
                            max_sigma_degrees(d,0.9)/2,rel_tol=1e-12)
    return records


def main():
    p=argparse.ArgumentParser()
    p.add_argument("--noise-deg",type=float,default=1.5)
    p.add_argument("--target",type=float,default=0.9)
    p.add_argument("--depth",type=int,default=6)
    p.add_argument("--audit",action="store_true")
    a=p.parse_args()
    rows=[dict(depth=d,gates=3*4**d,
               expected_halftrace=expected_halftrace(d,a.noise_deg),
               max_noise_degrees=max_sigma_degrees(d,a.target))
          for d in range(a.depth+1)]
    print(json.dumps(dict(model="independent isotropic Gaussian gate errors",
                          rows=rows,audit=audit() if a.audit else None),indent=2))


if __name__=="__main__":
    main()
