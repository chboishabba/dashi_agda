#!/usr/bin/env python3
"""J31 exact outward interval eighth-order chronological tangent microcharts.

Uses the actual nine-state physical smooth branches, not the seven long
original maps. Six independent positive-duration t0/t1 guard microcharts,
initial source chart fixed at t=0. The six actual event roots remain external
J29/J30 source receipts; the sixth event state is not J24-admitted.
"""
from fractions import Fraction as F
from math import factorial
import argparse,json
from pathlib import Path
import check_smith_filsinger_j31_native_seven_shortcharts_interval_20261124 as src
I=src.I

# The final sixth diode-off event's signed guard derivative requires narrow
# u,b (indices 2,4); source quadrature r (index 6) needs a larger tube.
LAST_RADII=tuple(map(F,('.0015','.0015','.0015','.0015','.0015','.006','.012','.003','.003')))


def matmul(a,b):
 n=len(a);assert n==len(b)==9 and all(len(row)==9 for row in a+b)
 return [[sum((a[i][k]*b[k][j] for k in range(n)),I(0)) for j in range(n)] for i in range(n)]

def pb8(J,h,N=8):
 """Time ordered noncommutative product: shared full-time J(X) interval.

 Terms each have interval enclosure of the ordered J(t1)..J(tn) simplex.
 The scalar n-simplex volume h^n/n! and grid rounding apply in every entry.
 No assertion J(t1)..J(tn) commute, or J(t) is constant.
 """
 assert 1<=N<=12 and isinstance(h,I) and h.a>0
 L=max(sum(x.mag() for x in row) for row in J)
 q=L*h.b
 assert q<F(1)
 # Bound sum_{n=N+1}∞ q^n/n! by exact geometric ratio.
 err=q**(N+1)/factorial(N+1)/(1-q/F(N+2))
 out=[[I(int(i==j)) for j in range(9)] for i in range(9)]
 power=[[I(int(i==j)) for j in range(9)] for i in range(9)]
 H=[[x*h for x in row] for row in J]
 for n in range(1,N+1):
  power=matmul(power,H)
  out=[[out[i][j]+power[i][j]/F(factorial(n)) for j in range(9)] for i in range(9)]
 out=[[z+I(-err,err) for z in row] for row in out]
 # First-order J + crude full Peano-Baker is an independent outer envelope.
 crude=q*q/(1-q)
 first=[[I(int(i==j))+h*J[i][j]+I(-crude,crude) for j in range(9)] for i in range(9)]
 assert all(out[i][j].within(first[i][j],strict=False) for i in range(9) for j in range(9))
 return out,err,first,L,q


def certify(k, h, clock_radius=None, source_halfwidth=F('0.0001')):
 """Certify genuine local two-time and state box on the actual source mode."""
 assert 0<=k<7
 t0=F(src.TIMES[k]); x0=list(map(F,src.STATES[k]));mode=src.MODES[k];h=F(h)
 dt=(F(0) if k==0 else F('0.0002') if k==6 else F('0.000005')) if clock_radius is None else F(clock_radius)
 assert k==0 and dt==0 or k>0 and dt>0
 if k>0:
  lo,hi=map(F,src.BRACKETS[k-1]);assert t0-dt<lo<hi<t0+dt
 time0=I(t0-dt,t0+dt)
 time1=I(t0+h-dt,t0+h+dt)
 # Genuine rectangular start/end time region; no correlated duration hypothesis.
 dur=time1-time0;assert dur.a>0
 fulltime=I(t0-dt,t0+h+dt)
 radii=LAST_RADII if k==6 else (F('0.001'),)*9
 X0=[I(c-source_halfwidth,c+source_halfwidth) for c in x0]
 X=[I(c-r,c+r) for c,r in zip(x0,radii)]
 ff,J=src.fJ(X,fulltime,mode)
 pic=[v+I(0,dur.b)*w for v,w in zip(X0,ff)]
 assert all(v.within(w) for v,w in zip(pic,X)), ('Picard',k)
 sol,err,old,L,q=pb8(J,dur)
 left=src.f(X0,time0,mode)
 right=src.f(X,time1,mode)
 start_time=[-sum((sol[i][j]*left[j] for j in range(9)),I(0)) for i in range(9)]
 # Enclose source-integral second-order Taylor using fulltime f, f_t + Df*f.
 sn,co=src.phase(fulltime)
 dft=[I(0) for _ in range(9)]
 dft[5]=-src.PARAM['omega']*src.K*sn
 dft[6]=-src.PARAM['omega']*src.K*co
 acceler=[dft[i]+sum((J[i][j]*ff[j] for j in range(9)),I(0)) for i in range(9)]
 end=[X0[i]+dur*left[i]+dur.square()/F(2)*acceler[i] for i in range(9)]
 assert all(y.within(w,strict=False) for y,w in zip(end,X))
 last=k-1
 u,v,chi=mode
 gu=src.guard(3,X);gv=src.guard(0,X)
 if last not in (3,5):assert gu.a>0 if u else gu.b<0
 if last not in (0,4):assert gv.a>0 if v else gv.b<0
 if chi:assert (X[4]-F('0.0018')).a>0
 else:assert (X[4]-F('0.006')).b<0
 slope=[]
 if k:
  pre=src.guard_slope(last,src.f(X,fulltime,src.MODES[last]))
  post=src.guard_slope(last,ff)
  sign=src.SIGNS[last]
  assert (pre.a>0 if sign>0 else pre.b<0)
  assert (post.a>0 or post.b<0)
  slope=[pre.record(),post.record()]
 return dict(chart=k,mode=list(mode),h=str(h),time0=time0.record(),time1=time1.record(),duration=dur.record(),
  input_state_radius=str(source_halfwidth),tube_radii=list(map(str,radii)),
  signed_source_guard_slopes=slope,source_J24_state_box_paid_by_J29=k in (1,2,3,4,5),
  source_sixth_J24_state_box_unpaid=k==6,original_exact_ode_root_receipts_external=k>0,
  source_picard_inward=True,source_non_switching_guards_strict=True,
  absolute_time_independence=(k!=0),original_clock_fixed_at_zero=k==0,
  tangent_PB_order=8,source_PB8_tail_radius=str(err),source_original_PB1_tail_radius=str(q*q/(1-q)),
  q=str(q),L=str(L),
  source_PB8_subset_PB1_81_entries=True,
  original_9D_terminal_Taylor2=[x.record() for x in end],
  original_9x9_source_variational_PB8=[[x.record() for x in row] for row in sol],
  source_partial_t0=[x.record() for x in start_time],source_partial_t1=[x.record() for x in right],
  full_original_segment_proved=False,original_69D_DF_proved=False,periodic_fixed_point_proved=False)

def adversarial_isotropic_last_guard():
    """A broad isotropic tube is Picard-admissible but LOSES pre-U-off sign."""
    k=6;t=F(src.TIMES[k]);x=list(map(F,src.STATES[k]))
    tr=F('0.0002');h=F('0.0005')
    X0=[I(c-F('0.0001'),c+F('0.0001')) for c in x]
    X=[I(c-F('0.01'),c+F('0.01')) for c in x]
    window=I(t-tr,t+tr+h)
    ff,_=src.fJ(X,window,src.MODES[k])
    pic=[X0[i]+I(0,h+2*tr)*ff[i] for i in range(9)]
    assert all(z.within(w) for z,w in zip(pic,X))
    pre=src.guard_slope(5,src.f(X,window,src.MODES[5]))
    assert pre.a<0<pre.b
    # This is a negative control: the PicarD tube alone does NOT pay
    # the signed physical pre-event guard required at the sixth root.
    return dict(isotropic_picard_admissible=True,
        isotropic_pre_guard_sign_certified=False,
        isotropic_pre_guard_straddles_zero=pre.record(),
        anisotropic_required=True)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True)
 a=ap.parse_args()
 results=[]
 for k in range(7):
  step=F('0.0005') if k==6 else F(1,8192) if k in (0,4,5) else F(1,16384)
  results.append(certify(k,step))
 summary=dict(status='PASS_SOURCE_7_PICARD_6_GENUINE_INDEPENDENT_TIME_PB8_NOT_LONG_69D',
  real_source_modes=7,strict_source_Picard_tubes=7,source_PB8_noncommuting_9x9_microtangents=7,
  genuine_independent_two_time_rectangles=6,source_initial_fixed_clock=1,
  exact_signed_guard_pair_microcharts=6,last_spark_slope_sign_reversal_retained=True,
  source_shortchart_sixth_event_state_physically_attached=False,
  full_physical_seven_source_segments_proved=False,
  original_69D_full_source_interval_DF_proved=False,original_strict_Krawczyk=False,
  periodic_orbit_proved=False,github_ci_used=False,agda_kernel=False,
  negative_control=adversarial_isotropic_last_guard(),charts=results)
 a.out.parent.mkdir(parents=True,exist_ok=True)
 a.out.write_text(json.dumps(summary,indent=2)+'\n')
 print(json.dumps({k:summary[k] for k in ('status','real_source_modes','genuine_independent_two_time_rectangles','source_PB8_noncommuting_9x9_microtangents')},indent=2))
 for x in results:
  print(x['chart'],'q',float(F(x['q'])),'tail8',float(F(x['source_PB8_tail_radius'])),
   'old',float(F(x['source_original_PB1_tail_radius'])))

if __name__=='__main__':main()
