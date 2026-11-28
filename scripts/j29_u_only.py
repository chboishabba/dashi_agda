#!/usr/bin/env python3
"""J29 physical V-deactivation handoff and U-active/V-inactive verified flow."""
from fractions import Fraction as F
from pathlib import Path
import json,sys
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent if HERE.name=='scripts' else HERE
sys.path.insert(0,str(HERE))
import j29_uv_active as z
w=z.w;v=z.v;c=z.c;p=z.p;I=z.I;S=z.S

def gv_slope(X,U=True,V=False):
 f=z.f_rhs(F('4.32383'),F('4.32385'),X,U,V)
 return f[3]-f[4]

def handoff(fifth,base):
 assert fifth['fifth_J24_full_nine_paid']
 tl,tr=map(F,fifth['event_t_bracket']);dt=tr-tl
 h=tr-F(base['t'])
 # Virtual source U+V active through the event, mathematically continued.
 virtual=z.step_uv(base,h,U_on=True,V_on=True,bracket_guard='V')
 event=[I(int(a),int(b),raw=True) for a,b in fifth['event_state_grid']]
 tube=[q.expand(F('.0001')) for q in event]
 rhs_pre=z.f_rhs(tl,tr,tube,True,True)
 rhs_post=z.f_rhs(tl,tr,tube,True,False)
 assert all((q+I(0,dt)*f).subset(T) for q,f,T in zip(event,rhs_pre,tube))
 assert all((q+I(0,dt)*f).subset(T) for q,f,T in zip(event,rhs_post,tube))
 assert (tube[2]-tube[4]-p['Vd']).a>0
 assert (tube[4]-p['Voff']).a>0
 sl_pre=gv_slope(tube,True,True)
 sl_post=gv_slope(tube,True,False)
 assert sl_pre.b<0 and sl_post.b<0
 assert sl_pre.a>-S # |V guard slope|<1
 J=z.J_signed(tube,True,False)
 L=max(map(sum,z.majorant(J)))
 assert L*dt<F(1,2)
 jv_bound=dt/F('.12')
 forcing=F(2)*jv_bound
 err=dt*forcing/(1-L*dt)
 assert err<F('0.000000001'),float(err)
 rem=[w.up(F(x)+F('0.000000001')) for x in virtual['remainder']]
 virtual['status']='J29_PASS_FIFTH_V_OFF_HANDOFF_CORRELATED'
 virtual['nsteps']=0
 virtual['remainder']=list(map(str,rem))
 virtual['handoff_virtual_UV_to_physical_U_only_error']=str(err)
 virtual['handoff_time_uncertainty']=str(dt)
 virtual['two_Picard_inclusions']=True
 virtual['U_active_V_inactive_source']=True
 virtual['fifth_J24_box_paid']=True
 return virtual

def guard_slope_taylor(P,J,Eflow,eps,h):
 # g_U'= d(u_poly-b_poly)/dt + residual difference plus Jacobian error.
 # The direct separate-coordinate interval f_u(X)-f_b(X) loses correlation.
 derivative=[(P[2][k+1]-P[4][k+1])*I(k+1) for k in range(len(P[2])-1)]
 polynomial=c.evalpoly(derivative,I(0,h))
 error=sum((w.mag(J[2][k]-J[4][k])*Eflow[k] for k in range(9)),F(0))+eps[2]+eps[4]
 return polynomial.expand(error)

def step(x,h,bracket_u=False):
 # Adapt the original two-track step: V inactive field, diode U active.
 t=F(x['t']);root=list(map(F,x['root']));noise=list(map(F,x['symbol_radii']));rem=[w.up(k) for k in x['remainder']]
 H=[[w.decode(k) for k in row] for row in x['H']]
 envelope=[sum((w.mag(k)*a for k,a in zip(row,noise)),rem[i]) for i,row in enumerate(H)]
 P,eps=z.residual_uv(52,t,root,h,U_on=True,V_on=False)
 for rr in ('.000001','.00001','.0001','.001'):
  R=F(rr);X=[c.evalpoly(row,I(0,h)).expand(R) for row in P]
  J=z.J_signed(X,U_on=True,V_on=False);A=z.majorant(J)
  Eflow=c.bound_exp(A,h,envelope,eps)
  # Guard-specific polynomial evaluation preserves shared time dependence.
  # State errors are enclosed independently but added exactly afterward.
  def guard_poly(idx,threshold):
   coeff=[P[idx][k]-P[4][k]-(threshold if k==0 else I(0)) for k in range(len(P[idx]))]
   return c.evalpoly(coeff,I(0,h)).expand(Eflow[idx]+Eflow[4])
  gu=guard_poly(2,p['Vd']);gv=guard_poly(3,p['Vd'])
  gs=c.evalpoly([P[4][k]-(p['Voff'] if k==0 else I(0)) for k in range(len(P[4]))],I(0,h)).expand(Eflow[4])
  valid=all(a<R for a in Eflow) and gs.a>0
  slope=guard_slope_taylor(P,J,Eflow,eps,h)
  if bracket_u:valid=valid and slope.b<0
  else:valid=valid and gu.a>0
  startbox=[I(r).expand(e) for r,e in zip(root,envelope)]
  startgv=startbox[3]-startbox[4]-p['Vd']
  # Strictly decreasing guard + strict negative start excludes reactivation,
  # even when independent full-slab u/v/b coordinate intervals overlap.
  valid=valid and (gv.b<0 or (gv_slope(X).b<0 and
          (startgv.b<0 or x.get('nsteps',0)==0)))
  if valid:break
 else:raise AssertionError(('physical Uonly flow tube fail',str(t),str(h),float(max(Eflow)),float(gu.a/S),float(gv.b/S)))
 Phi,_,tail=v.exp_bound_signed(J,h,8)
 Hnew=v.mmul(Phi,H)
 force=c.bound_exp(A,h,[F(0)]*9,eps)
 rnew=[sum((w.mag(k)*a for k,a in zip(row,rem)),f) for row,f in zip(Phi,force)]
 polyend=[c.evalpoly(row,I(h)) for row in P]
 rootnext,roundoff=c.rational_recenter(polyend)
 remnext=[w.up(a+b) for a,b in zip(rnew,roundoff)]
 Eend=[sum((w.mag(k)*a for k,a in zip(row,noise)),r) for row,r in zip(Hnew,remnext)]
 assert all(a<R for a in Eend)
 enclose=[q.expand(e) for q,e in zip(polyend,Eend)]
 ge=enclose[2]-enclose[4]-p['Vd']
 projected_uncertainty=(sum((w.mag(a-b)*r for a,b,r in zip(Hnew[2],Hnew[4],noise)),F(0))
                        +remnext[2]+remnext[4])
 projected_guard=(I(rootnext[2]-rootnext[4])-p['Vd']).expand(projected_uncertainty)
 return dict(status='J29_U_ONLY_VALIDATED_STEP',t=str(t+h),nsteps=x['nsteps']+1,
  root=list(map(str,rootnext)),symbol_radii=list(map(str,noise)),
  remainder=list(map(str,remnext)),H=[[w.encode(k) for k in row] for row in Hnew],
  last=dict(max_error=float(max(Eend)),max_flow_error=float(max(Eflow)),U_guard_end=[str(ge.a),str(ge.b)],U_guard_end_affine=[str(projected_guard.a),str(projected_guard.b)],
    U_guard_slope=[str(slope.a),str(slope.b)],
    V_upper=float(gv.b/S),spark_lower=float(gs.a/S),R=str(R),tail=float(tail)))

def advance(x,count=10):
 for i in range(count):
  x=step(x,F('.01'))
  print(x['nsteps'],float(F(x['t'])),x['last']['max_error'],flush=True)
 return x

def main():
 import argparse
 ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['handoff','advance','event_u']);ap.add_argument('--fifth');ap.add_argument('--base');ap.add_argument('--input');ap.add_argument('--out',required=True);ap.add_argument('--count',type=int,default=10)
 a=ap.parse_args()
 if a.mode=='handoff':x=handoff(json.loads(Path(a.fifth).read_text()),json.loads(Path(a.base).read_text()))
 elif a.mode=='event_u':x=isolate_last(json.loads(Path(a.input).read_text()))
 else:x=advance(json.loads(Path(a.input).read_text()),a.count)
 Path(a.out).write_text(json.dumps(x,indent=2)+'\n');print('STATUS',x['status'],x.get('t',x.get('t_bracket')))

def isolate_last(data):
 assert data['nsteps']==60
 t=F(data['t']);root=list(map(F,data['root']));noise=list(map(F,data['symbol_radii']));rem=[w.up(q) for q in data['remainder']]
 H=[[w.decode(q) for q in row] for row in data['H']]
 envelope=[sum((w.mag(z)*n for z,n in zip(row,noise)),rem[i]) for i,row in enumerate(H)]
 cache={}
 def at(h):
  if h not in cache:
   q=step(data,h,bracket_u=True)
   cache[h]=(list(map(int,q['last']['U_guard_end_affine'])),q)
  return cache[h]
 left,right=F('.004'),F('.006')
 assert at(left)[0][0]>0 and at(right)[0][1]<0
 decisions=[]
 for k in range(24):
  mid=(left+right)/2
  bounds,_=at(mid)
  if bounds[0]>0:left=mid;deci='L'
  elif bounds[1]<0:right=mid;deci='R'
  else:deci='unknown';decisions.append((str(mid),deci));break
  decisions.append((str(mid),deci))
 assert at(left)[0][0]>0 and at(right)[0][1]<0
 h=right
 P,eps=z.residual_uv(52,t,root,h,True,False)
 for rr in ('.00001','.0001','.001'):
  R=F(rr);X=[c.evalpoly(row,I(0,h)).expand(R) for row in P]
  J=z.J_signed(X,True,False);A=z.majorant(J)
  Eflow=c.bound_exp(A,h,envelope,eps)
  u=guard_slope_taylor(P,J,Eflow,eps,h)
  V=(X[3]-X[4]-p['Vd'])
  spark=(X[4]-p['Voff'])
  if all(q<R for q in Eflow) and u.b<0 and V.b<0 and spark.a>0:break
 else:raise AssertionError('last event smooth tube unsuccessful')
 whole=[c.evalpoly(row,I(left,right)).expand(e) for row,e in zip(P,Eflow)]
 source=json.loads((ROOT/'Artifacts/smith-filsinger/j24_six_hybrid_guard_centres_20261123.json').read_text(),parse_float=F,parse_int=F)['events']
 assert source[5]['kind']=='diode' and source[5]['name']=='U'
 members=[x.subset(I(s-F('.0001'),s+F('.0001'))) for x,s in zip(whole,source[5]['x'])]
 return dict(status='J29_SIXTH_ROOT_UNIQUE_ALL_J24_BOXES' if all(members) else 'J29_SIXTH_ROOT_UNIQUE_LAST_J24_BOX_PENDING',
   t_bracket=[str(t+left),str(t+right)],time_width_model=str(right-left),
   left_guard_grid=list(map(str,at(left)[0])),right_guard_grid=list(map(str,at(right)[0])),
   signed_U_derivative_grid=[str(u.a),str(u.b)],
   V_remains_inactive=True,spark_remains_ON=True,
   event_state_grid=[[str(x.a),str(x.b)] for x in whole],
   J24_original_last_box_coordinate_membership=members,
   J24_original_last_box_paid=all(members),J24_boxes_paid=6 if all(members) else 5,
   validated_crossings=6,
   all_time_error_max=float(max(Eflow)),
   exact_integer_directed_rounding_grid='10^30',
   bisection_trace=decisions,
   post_U_OFF_physical_flow_not_integrated=True,
   fundamental_period_return_not_certified=True,
   exact_periodic_orbit_proved=False,
   original_environmental_source_measured=False,CI_used=False)

if __name__=="__main__":main()
