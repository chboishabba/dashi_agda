#!/usr/bin/env python3
"""Fail-closed source experiment: naïve first k4 full-length 1/6 step loses physical diode signs."""
from fractions import Fraction as F
import json,argparse
from pathlib import Path
import check_smith_filsinger_j31_pb8_anisotropic_six_time_20261124 as pp
s=pp.src;I=s.I

def audit():
 k=4;a=F(s.TIMES[k]);b=F(s.TIMES[k+1]);dt=F('0.000005')
 t0=I(a-dt,a+dt);t1=I(a+(b-a)/6)
 dur=t1-t0;assert dur.a>0
 x=[F(z) for z in s.STATES[k]]
 initial=[I(y-F('0.0001'),y+F('0.0001')) for y in x]
 mids=x;radii=[F('0.000101')]*9
 for j in range(100):
  tube=[I(c-r,c+r) for c,r in zip(mids,radii)]
  f,J=s.fJ(tube,I(t0.a,t1.b),s.MODES[k])
  need=[F('0.0001')+dur.b*z.mag() for z in f]
  future=[max(r,F(101,100)*w) for r,w in zip(radii,need)]
  if future==radii:break
  radii=future
 else:raise AssertionError('negative-control tube did not converge')
 tube=[I(c-r,c+r) for c,r in zip(mids,radii)]
 f,J=s.fJ(tube,I(t0.a,t1.b),s.MODES[k])
 included=all((initial[z]+I(0,dur.b)*f[z]).within(tube[z]) for z in range(9))
 v=s.guard(4,tube);u=s.guard(3,tube);vprime=s.guard_slope(4,f)
 assert included and v.a<0<v.b and u.a<0<u.b and vprime.a<0<vprime.b
 return dict(status='PASS_NAIVE_SOURCE_PICARD_BUT_FAIL_SOURCE_PHYSICAL_GUARDS',
  source_segment='event4 U ON to event5 V OFF',compared_to='32-slab centre+residual exact source',
  naive_first_slab_duration=dur.record(),strict_picard_valid=True,
  U_ON_guard_sign_certified=False,V_ON_guard_sign_certified=False,
  V_OFF_guard_slope_sign_certified=False,
  U_guard=u.record(),V_guard=v.record(),V_slope=vprime.record(),
  no_original_periodic_orbit_claim=True)

def main():
 p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args()
 x=audit();a.out.parent.mkdir(parents=True,exist_ok=True)
 a.out.write_text(json.dumps(x,indent=2)+'\n');print(x['status'])
if __name__=='__main__':main()
