#!/usr/bin/env python3
"""J30 final continuous U-off event handoff and no-diode physical return.

No claim of a periodic point; proof initial state is rational J23 seed.  Uses
source-preserving J29 exact rational, affine label and interval ODE machinery.
"""
import json,math,argparse
from pathlib import Path
from fractions import Fraction as F
import j29_u_only as y
z=y.z;w=y.w;v=y.v;c=y.c;I=y.I;S=y.S;p=y.p
ROOT=Path(__file__).resolve().parents[1]

def atan_alternating(x,n=26):
 x=F(x); partial=sum(((-1)**k*x**(2*k+1)/F(2*k+1) for k in range(n)),F(0))
 term=x**(2*n+1)/F(2*n+1)
 return (partial,partial+term) if n%2==0 else (partial-term,partial)

def tau_interval():
 a,b=atan_alternating(F(1,5));d,e=atan_alternating(F(1,239))
 pi_l=16*a-4*e;pi_u=16*b-4*d
 lo=F(20,11)*pi_l;hi=F(20,11)*pi_u
 assert F('5.71')<lo<hi<F('5.72')
 assert hi-lo<F(1,10**28)
 return lo,hi

def checked_event_handoff(source):
 assert source['nsteps']==60
 t0=F(source['t']);rece=json.loads((ROOT/'receipts/J29_SIXTH_MVT_REFINED.json').read_text())
 tl,tr=map(F,rece['mean_value_refined_bracket']);dt=tr-tl
 assert dt<F('0.000368')
 ref=y.step(source,tr-t0,bracket_u=True)
 # Same fixed endpoint in old virtual U-active smooth extension.
 assert F(ref['t'])==tr
 root=list(map(F,source['root']));noise=list(map(F,source['symbol_radii']))
 rem=list(map(F,source['remainder']));H=[[w.decode(z) for z in row] for row in source['H']]
 envelope=[sum((w.mag(k)*n for k,n in zip(row,noise)),rem[i]) for i,row in enumerate(H)]
 h=tr-t0
 P,eps=z.residual_uv(52,t0,root,h,True,False)
 for rr in ('.0001','.001','.01'):
  R=F(rr);X=[c.evalpoly(row,I(0,h)).expand(R) for row in P]
  J=z.J_signed(X,True,False)
  E=c.bound_exp(z.majorant(J),h,envelope,eps)
  slope=y.guard_slope_taylor(P,J,E,eps,h)
  if all(k<R for k in E) and slope.b<0:break
 else: raise AssertionError('failed pre-event uniform tube')
 # Important: true actual switching time belongs to (tl,tr), and no jump in state.
 # Both mode extensions on the same tube have admissible initial states.
 origin=[c.evalpoly(row,I(tl-t0,tr-t0)).expand(e) for row,e in zip(P,E)]
 for radius in ('.01','.03','.1','.2'):
  bubble=[q.expand(F(radius)) for q in origin]
  fp=z.f_rhs(tl,tr,bubble,True,False);fm=z.f_rhs(tl,tr,bubble,False,False)
  ok=(all((q+I(0,dt)*f).subset(tube) for q,f,tube in zip(origin,fp,bubble))
    and all((q+I(0,dt)*f).subset(tube) for q,f,tube in zip(origin,fm,bubble)))
  if ok:break
 assert ok,'both smooth-mode local Picard tubes failed'
 assert (bubble[3]-bubble[4]-p['Vd']).b<0
 assert (bubble[4]-p['Voff']).a>0
 # The virtual U-on guard after the root is small by g'_U<0 on [tl,tr].
 gprime_virtual=(fp[2]-fp[4]);gprime_physical=(fm[2]-fm[4])
 assert slope.b<0 and gprime_physical.b<0
 # U-active field -- U-off field = jU times fixed vector with max norm < 2*jU.
 # g_U(virtual) falls from 0 at t* so |g_U(virtual)| <= |g'_U|_max*(tr-tl).
 g_slope_max=w.mag(slope)
 bound_force=2*g_slope_max*dt/F('.12')
 L=max(map(sum,z.majorant(z.J_signed(bubble,False,False))))
 assert L*dt<F(1,2)
 error=dt*bound_force/(1-L*dt)
 assert error<F('0.000001'),(float(error),float(L))
 ref['status']='J30_PASS_CORRELATED_U_OFF_HANDOFF'
 ref['nsteps']=0
 ref['remainder']=[str(w.up(F(x)+F('0.000001'))) for x in ref['remainder']]
 ref['event_time_bracket']=[str(tl),str(tr)]
 ref['true_handoff_state_error_bound']=str(error)
 ref['exact_Picard_both_smooth_modes']=True
 ref['physical_U_off_V_off_justified_by_derivative']=True
 ref['final_original_J24_sixth_event_state_box_paid']=False
 return ref

def no_diode_step(x,h,first=False):
 t=F(x['t']);h=F(h)
 root=list(map(F,x['root']));noise=list(map(F,x['symbol_radii']))
 rem=[w.up(v) for v in x['remainder']]
 H=[[w.decode(k) for k in row] for row in x['H']]
 envelope=[sum((w.mag(k)*n for k,n in zip(row,noise)),rem[i]) for i,row in enumerate(H)]
 P,eps=z.residual_uv(52,t,root,h,False,False)
 for rr in ('.00001','.0001','.001','.01'):
  R=F(rr);X=[c.evalpoly(row,I(0,h)).expand(R) for row in P]
  J=z.J_signed(X,False,False);A=z.majorant(J)
  Eflow=c.bound_exp(A,h,envelope,eps)
  slope=y.guard_slope_taylor(P,J,Eflow,eps,h)
  def guard(idx,th):
   q=[P[idx][j]-P[4][j]-(th if j==0 else I(0)) for j in range(len(P[idx]))]
   return c.evalpoly(q,I(0,h)).expand(Eflow[idx]+Eflow[4])
  gu=guard(2,p['Vd']);gv=guard(3,p['Vd']);gs=c.evalpoly([q-(p['Voff'] if j==0 else I(0)) for j,q in enumerate(P[4])],I(0,h)).expand(Eflow[4])
  good=(all(e<R for e in Eflow) and gv.b<0 and gs.a>0 and
        (gu.b<0 or (first and slope.b<0)))
  if good:break
 else:
  raise AssertionError(('no diode validated slab failed',str(t),str(h),float(max(Eflow)),float(gu.b/S),float(gv.b/S),float(slope.b/S)))
 Phi,_,tail=v.exp_bound_signed(J,h,8)
 Hnext=v.mmul(Phi,H)
 f=c.bound_exp(A,h,[F(0)]*9,eps)
 rnext=[sum((w.mag(k)*e for k,e in zip(row,rem)),ee) for row,ee in zip(Phi,f)]
 end=[c.evalpoly(row,I(h)) for row in P]
 rootnext,roundoff=c.rational_recenter(end)
 remnext=[w.up(ee+ro) for ee,ro in zip(rnext,roundoff)]
 err=[sum((w.mag(k)*e for k,e in zip(row,noise)),remnext[i]) for i,row in enumerate(Hnext)]
 assert all(e<R for e in err)
 guend=(I(rootnext[2]-rootnext[4])-p['Vd']).expand(err[2]+err[4])
 return dict(status='J30_PASS_NODIODE_SMOOTH_SLAB',t=str(t+h),nsteps=x['nsteps']+1,
  root=list(map(str,rootnext)),symbol_radii=list(map(str,noise)),remainder=list(map(str,remnext)),
  H=[[w.encode(k) for k in row] for row in Hnext],
  sixth_event_original_J24_box_paid=False,
  last=dict(error_max=float(max(err)),fulltime_error=float(max(Eflow)),
   U_guard_whole=[str(gu.a),str(gu.b)],V_guard_whole=[str(gv.a),str(gv.b)],
   ON_guard_whole=[str(gs.a),str(gs.b)],U_guard_end=[str(guend.a),str(guend.b)],
   U_slope_whole=[str(slope.a),str(slope.b)],signed_Peano_tail=float(tail),radius=str(R)))

def advance(x,count=10,step=F('0.01')):
 for n in range(count):
  x=no_diode_step(x,step,first=(x['nsteps']==0))
  print(x['nsteps'],float(F(x['t'])),x['last']['error_max'],x['last']['U_guard_end'],flush=True)
 return x

def main():
 ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['handoff','advance','finish']);ap.add_argument('--input');ap.add_argument('--count',type=int,default=10);ap.add_argument('--out',required=True)
 a=ap.parse_args()
 if a.mode=='handoff':
  x=checked_event_handoff(json.loads((ROOT/'receipts/J29_U_60.json').read_text()))
 elif a.mode=='advance':
  x=advance(json.loads(Path(a.input).read_text()),a.count)
 else:
  x=json.loads(Path(a.input).read_text())
  exact_tl,exact_tu=tau_interval()
  # Rational *grid* lower/upper times derived by outward floor/ceil
  # from exact rational Machin bounds, avoiding irrational-length Taylor recurrences.
  grid=10**16
  tl=F((exact_tl.numerator*grid)//exact_tl.denominator,grid)
  tu=F(-((-exact_tu.numerator*grid)//exact_tu.denominator),grid)
  assert tl<=exact_tl<exact_tu<=tu and tu-tl<=F(2,grid)
  dt=tl-F(x['t'])
  assert 0<dt<F('0.011')
  x=no_diode_step(x,dt)
  # Extend the validated no-diode solution from rational lower tau to actual irrational tau.
  # tiny remaining [tl,tu] is enclosed by interval smooth Picard bootstrap.
  e0=[sum((w.mag(w.decode(z))*F(n) for z,n in zip(row,x['symbol_radii'])),F(r))
      for row,r in zip(x['H'],x['remainder'])]
  B=[I(F(r)).expand(e) for r,e in zip(x['root'],e0)]
  width=tu-tl
  tube=[b.expand(F('0.00001')) for b in B]
  rhs=z.f_rhs(tl,tu,tube,False,False)
  assert all((b+I(0,width)*f).subset(T) for b,f,T in zip(B,rhs,tube))
  assert (tube[2]-tube[4]-p['Vd']).b<0 and (tube[3]-tube[4]-p['Vd']).b<0
  assert (tube[4]-p['Voff']).a>0
  end=[b+I(0,width)*f for b,f in zip(B,rhs)]
  x=dict(status='J30_PASS_NOMINAL_FULL_TAU_RETURN_ENCLOSURE_NOT_FIXED_POINT',
    source_initial_state=c.j25.ROOT,tau_interval=[str(tl),str(tu)],
    uncertainty_irrational_tau_width=str(width),
    return_state_grid=[[str(q.a),str(q.b)] for q in end],
    initial_root_is_periodic_proved=False,exact_nine_state_return_enclosed=True,
    interval_derivative_not_proved=True,original_J24_sixth_box_not_proved=True)
 Path(a.out).write_text(json.dumps(x,indent=2)+'\n')
 print('STATUS',x['status'],'t',x.get('t',x.get('tau_interval')),flush=True)

if __name__=='__main__':main()
