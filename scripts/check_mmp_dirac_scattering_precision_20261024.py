#!/usr/bin/env python3
"""Cutoff-vs-discretization audit for effective Dirac scattering (not 4D MMP)."""
import json, math
from pathlib import Path
from check_mmp_dirac_flux_scattering_20261024 import geometry,scattering

cases=[]
for cutoff in (120.,240.,480.):
    profile,Z,geo=geometry(cutoff=cutoff,n_outer=1601)
    item={'cutoff_radius':cutoff,'energies':{}}
    for E in (.2,.4,.55):
        entry={}
        for n in (1,2):
            fac=math.sqrt(n*(n+12))
            d=scattering(E,lambda z,fac=fac:fac*profile(z),-Z,Z,h=.18,endpoint_mass=fac*float(profile(Z)))
            entry[str(n)]={'T':d['T'],'R':d['R'],'probability_error':d['probability_error']}
        item['energies'][str(E)]=entry
    cases.append(item)
    print('cutoff',cutoff,'n1 T(E=.2)',item['energies']['0.2']['1']['T'],
          'n2 T(E=.2)',item['energies']['0.2']['2']['T'])
pref,Z,geo=geometry(cutoff=240.)
refine=[]
for step in (.3,.15,.075):
    d=scattering(.55,lambda z:math.sqrt(28)*pref(z),-Z,Z,h=step,endpoint_mass=math.sqrt(28)*float(pref(Z)))
    refine.append({'step':step,'T':d['T'],'flux_error':d['flux_error']})
assert abs(refine[0]['T']-refine[-1]['T'])<4e-5
assert abs(refine[1]['T']-refine[-1]['T'])<6e-6
assert all(d['flux_error']<3e-8 for d in refine)
# This is finite-cutoff STABILITY after local-mass matching, NOT Jost
# convergence to an analytically constructed infinity limit.
t1=[a['energies']['0.2']['1']['T'] for a in cases]
t2=[a['energies']['0.2']['2']['T'] for a in cases]
assert max(t1)-min(t1)<6e-5
assert max(t2)-min(t2)<3e-7
assert max(t1)-min(t1)>1e-6, 'Finite boundary still affects scattering'
print('PASS: local-mass matched boundary strongly improves finite RN radius stability; infinite-radius Jost limit still OPEN')
Path(__file__).with_suffix('.json').write_text(json.dumps({'cutoff':cases,'grid_refinement':refine,
  'scope':'same effective fixed-state RN-cutoff approximation; no infinite-radius scattering proof'},indent=2))
