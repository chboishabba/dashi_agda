#!/usr/bin/env python3
"""Illustrative two-coil magnetic field via discretised Biot-Savart.

Not a measured device, coil/thermal/safety certification, magnetic material
model or levitation result. 3x3x3 samples are a grid, not mystical 27 sites.
"""
from math import cos, sin, pi, sqrt

MU0 = 4e-7*pi

def loop_b(x, y, z, radius_m, centre_z_m, turns, ampere, steps=256):
    """Approximate ideal thin-wire ring B [tesla]; do not sample on the wire."""
    if radius_m <= 0 or steps < 24:
        raise ValueError('invalid geometry or integration resolution')
    sumx = sumy = sumz = 0.0
    dt = 2*pi/steps
    for k in range(steps):
        t = (k+0.5)*dt
        xx, yy = radius_m*cos(t), radius_m*sin(t)
        dx, dy = -radius_m*sin(t)*dt, radius_m*cos(t)*dt
        rx, ry, rz = x-xx, y-yy, z-centre_z_m
        q = rx*rx + ry*ry + rz*rz
        if q < 1e-16:
            raise ValueError('sample near ideal thin wire')
        f = 1/(q*sqrt(q))
        sumx += dy*rz*f
        sumy += -dx*rz*f
        sumz += (dx*ry-dy*rx)*f
    scale = MU0*turns*ampere/(4*pi)
    return (scale*sumx, scale*sumy, scale*sumz)

def pair_b(x, y, z, *, radius_m=.10, separation_m=.10, turns=100,
           ampere=1.0, anti=False):
    left = loop_b(x, y, z, radius_m, -separation_m/2, turns, ampere)
    right = loop_b(x, y, z, radius_m, +separation_m/2, turns,
                   -ampere if anti else ampere)
    return tuple(a+b for a,b in zip(left,right))

def norm(v):
    return sqrt(sum(x*x for x in v))

def synthetic_report():
    radius, spacing, turns, current = .10, .10, 100, 1.0
    uniform = pair_b(0,0,0,radius_m=radius,separation_m=spacing,
                     turns=turns,ampere=current)
    analytic = MU0*turns*current*radius**2/(radius**2+(spacing/2)**2)**1.5
    assert abs(uniform[2]/analytic-1) < .0001
    assert abs(pair_b(0,0,0,anti=True)[2]) < 1e-14
    coords = (-.015, 0.0, .015)
    fields = [norm(pair_b(x,y,z)) for x in coords for y in coords for z in coords]
    h = .005
    gradient = (pair_b(0,0,h,anti=True)[2] -
                pair_b(0,0,-h,anti=True)[2])/(2*h)
    assert abs(gradient) > .001
    return {
        'illustrative_helmholtz_B_center_T': uniform[2],
        'analytic_B_center_T': analytic,
        'sample_sites': len(fields),
        'sample_min_T': min(fields),
        'sample_max_T': max(fields),
        'illustrative_antihelmholtz_dBz_dz_T_per_m': gradient,
        'real_coil_geometry_measured': False,
        'power_and_temperature_validated': False,
        'force_and_levitation_validated': False,
    }

if __name__ == '__main__':
    for k,v in synthetic_report().items():
        print(f'{k}: {v}')
