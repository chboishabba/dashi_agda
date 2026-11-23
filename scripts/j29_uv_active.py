#!/usr/bin/env python3
"""J29 validated uncertain U diode activation and physical U+V ON advance.

Requires proof of J29 4th event. Fully interval nominal source-only IVP;
real circuit or periodic point not verified. No CI.
"""
from fractions import Fraction as F
import math,json,argparse,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent if HERE.name=='scripts' else HERE
sys.path.insert(0,str(HERE))
import j29_affine_enclosure as w
v=w.v;c=w.c;I=w.I;S=w.S;p=v.p

def rhspoly(P,SS,CC,n,U_on=True,V_on=True):
 i,j,u,vo,b,q,r,ih,cap=P
 ci=lambda x:c.coef(x,n)
 a=-p['R1']*ci(i);bb=ci(u)-ci(vo)-p['R2']*ci(j)
 ju=((ci(u)-ci(b)-(p['Vd'] if n==0 else I(0)))/p['Rd']) if U_on else I(0)
 jv=((ci(vo)-ci(b)-(p['Vd'] if n==0 else I(0)))/p['Rd']) if V_on else I(0)
 left=-ci(j)-ju+p['k']*ci(q)+p['kh']*ci(ih)
 right=ci(j)-jv
 rho=p['gamma_rad']+p['gamma_internal']
 return [
   (p['L2']*a-p['M']*bb)/I('2.64'),
   (-p['M']*a+p['L1']*bb)/I('2.64'),
   (I('1.55')*left+right)/I('1.17'),
   (left+I('1.4')*right)/I('1.17'),
   (ju+jv-p['Gbleed']*ci(b)-ci(ih))/p['Cb'],
   p['omega']*ci(r)-rho*ci(q)-p['k']*ci(u)/I(2)+c.j25.RAD*p['source_amp']*c.coef(CC,n),
   -p['omega']*ci(q)-rho*ci(r)-c.j25.RAD*p['source_amp']*c.coef(SS,n),
   (ci(b)-ci(cap)-(p['Rcoil']+p['Rgap'])*ci(ih)-p['kh']*ci(u))/p['Lh']]

def poly_uv(N,t0,root,U_on=True,V_on=True):
 P=[[I(z)] for z in root];si,co=c.trig_exact(F('.3')+F('1.1')*t0)
 SS=[si];CC=[co]
 for n in range(N):
   d=rhspoly(P,SS,CC,n,U_on,V_on)
   cap=P[8];D=[];inv=[]
   for k in range(n+1):
     D.append((I(1) if k==0 else I(0))+I('1.5')*c.coeff(cap,cap,k))
     if k==0:inv.append(I(1)/D[0])
     else:inv.append(-sum((D[j]*inv[k-j] for j in range(1,k+1)),I(0))/D[0])
   dc=sum(((c.coef(P[7],m)-p['Gload']*c.coef(cap,m))*inv[n-m] for m in range(n+1)),I(0))/p['Ch']
   for seq,val in zip(P,d+[dc]):seq.append(val/I(n+1))
   SS.append(p['omega']*CC[n]/I(n+1));CC.append(-p['omega']*SS[n]/I(n+1))
 return P,SS,CC

def residual_uv(N,t0,root,h,U_on=True,V_on=True):
 P,SS,CC=poly_uv(N,t0,root,U_on,V_on)
 rr=[rhspoly(P,SS,CC,n,U_on,V_on) for n in range(N+1)]
 residual=[]
 for j in range(8):
  residual.append([(P[j][n+1]*I(n+1) if n+1<len(P[j]) else I(0))-rr[n][j] for n in range(N+1)])
 cap=P[8]
 D=[I('1.5')*z+(I(1) if k==0 else I(0)) for k,z in enumerate(c.mul(cap,cap))]
 cd=[z*I(k+1) for k,z in enumerate(cap[1:])]
 numerator=c.mul(D,cd)
 for k in range(len(numerator)):
  numerator[k]=p['Ch']*numerator[k]-(c.coef(P[7],k)-p['Gload']*c.coef(cap,k))
 bound=[c.evalabs(z,I(h)) for z in residual]
 bound.append(c.j25.ceil_div(c.evalabs(numerator,I(h))*S,p['Ch'].a))
 tail=I(0,F('.21')*F('1.1')**N*F(h)**N/F(math.factorial(N))).b
 bound[5]+=tail;bound[6]+=tail
 return P,[F(z,S) for z in bound]

def J_signed(X,U_on=True,V_on=True):
 J=v.jsigned(X)
 g=I(1)/p['Rd']
 if U_on:
  J[2][2]=J[2][2]-I('1.55')*g/I('1.17')
  J[2][4]=J[2][4]+I('1.55')*g/I('1.17')
  J[3][2]=J[3][2]-g/I('1.17')
  J[3][4]=J[3][4]+g/I('1.17')
  J[4][2]=J[4][2]+g/p['Cb']
  J[4][4]=J[4][4]-g/p['Cb']
 if not V_on:
  J[2][3]=J[2][3]+g/I('1.17')
  J[2][4]=J[2][4]-g/I('1.17')
  J[3][3]=J[3][3]+I('1.4')*g/I('1.17')
  J[3][4]=J[3][4]-I('1.4')*g/I('1.17')
  J[4][3]=J[4][3]-g/p['Cb']
  J[4][4]=J[4][4]+g/p['Cb']
 return J

def majorant(J):return [[w.mag(z) for z in row] for row in J]

def f_rhs(tlo,thi,X,U_on=True,V_on=True):
 i,j,u,vo,b,q,r,ih,cap=X
 sin,cos=v.j28.trig_interval(tlo,thi)
 ju=(u-b-p['Vd'])/p['Rd'] if U_on else I(0)
 jv=(vo-b-p['Vd'])/p['Rd'] if V_on else I(0)
 a=-p['R1']*i;bb=u-vo-p['R2']*j
 left=-j-ju+p['k']*q+p['kh']*ih;right=j-jv
 gam=p['gamma_rad']+p['gamma_internal']
 return [(p['L2']*a-p['M']*bb)/I('2.64'),
         (-p['M']*a+p['L1']*bb)/I('2.64'),
         (I('1.55')*left+right)/I('1.17'),
         (left+I('1.4')*right)/I('1.17'),
         (ju+jv-p['Gbleed']*b-ih)/p['Cb'],
         p['omega']*r-gam*q-p['k']*u/I(2)+c.j25.RAD*p['source_amp']*cos,
         -p['omega']*q-gam*r-c.j25.RAD*p['source_amp']*sin,
         (b-cap-(p['Rcoil']+p['Rgap'])*ih-p['kh']*u)/p['Lh'],
         (ih-p['Gload']*cap)/(p['Ch']*(I(1)+I('1.5')*cap**2))]

def gu_slope(X,U_on,V_on):
 # extract u' - b' from exact RHS at the same time, source doesn't enter these rows
 z=f_rhs(F('4.27548'),F('4.27550'),X,U_on,V_on)
 return z[2]-z[4]

def state_at_h_virtual(data,h):
  t=F(data['t']);root=list(map(F,data['root']))
  noise=list(map(F,data['symbol_radii']));rem=[w.up(q) for q in data['remainder']]
  H=[[w.decode(q) for q in row] for row in data['H']]
  envelope=[sum((w.mag(a)*b for a,b in zip(row,noise)),rem[i]) for i,row in enumerate(H)]
  P,eps=v.j27.residual_v(52,t,root,h)
  for rr in ('.000001','.00001','.0001'):
   R=F(rr);X=[c.evalpoly(row,I(0,h)).expand(R) for row in P]
   Eflow=c.bound_exp(v.j27.get_A_v(X),h,envelope,eps)
   if all(e<R for e in Eflow) and (X[3]-X[4]-p['Vd']).a>0 and (X[4]-p['Voff']).a>0:break
  else:raise AssertionError('virtual U-off tube failed')
  Phi,_,_=v.exp_bound_signed(v.jsigned(X),h,8)
  Hnew=v.mmul(Phi,H)
  forcing=c.bound_exp(v.j27.get_A_v(X),h,[F(0)]*9,eps)
  residual=[sum((w.mag(z)*a for z,a in zip(row,rem)),f) for row,f in zip(Phi,forcing)]
  centre_end=[c.evalpoly(row,I(h)) for row in P]
  root_end,roundoff=c.rational_recenter(centre_end)
  rem_end=[w.up(a+b) for a,b in zip(residual,roundoff)]
  return dict(root=root_end, H=Hnew,noise=noise,rem=rem_end,t=t+h,Eflow=Eflow)

def handoff(fourth,base):
  assert fourth['original_J24_fourth_box_paid']
  left,right=map(F,fourth['U_activation_time_bracket']);dt=right-left
  assert 0<dt<F(1,100000)
  reference=state_at_h_virtual(base,right-F(base['t']))
  state=[I(int(a),int(b),raw=True) for a,b in fourth['event_state_grid']]
  tube=[z.expand(F('.0001')) for z in state]
  pre=f_rhs(left,right,tube,False,True)
  post=f_rhs(left,right,tube,True,True)
  assert all((z+I(0,dt)*f).subset(T) for z,f,T in zip(state,pre,tube))
  assert all((z+I(0,dt)*f).subset(T) for z,f,T in zip(state,post,tube))
  assert (tube[3]-tube[4]-p['Vd']).a>0
  assert (tube[4]-p['Voff']).a>0
  slo_pre=gu_slope(tube,False,True);slo_post=gu_slope(tube,True,True)
  assert slo_pre.a>0 and slo_post.a>0
  assert slo_pre.b<S*2
  J=J_signed(tube,True,True)
  L=max(map(sum,majorant(J)))
  assert L*dt<F(1,2)
  jU_bound=F(2)*dt/F('.12')
  forcing_upper=F(2)*jU_bound
  err=dt*forcing_upper/(1-L*dt)
  assert err < F('0.000000001'),(float(err),float(L))
  rem=[w.up(z+F('0.000000001')) for z in reference['rem']]
  # Add source-verified uncertainty to remainder without collapsing symbols
  return dict(status='J29_PASS_FOURTH_U_HANDOFF_CORRELATED',t=str(right),nsteps=0,
    root=list(map(str,reference['root'])),symbol_radii=list(map(str,reference['noise'])),
    remainder=list(map(str,rem)),H=[[w.encode(z) for z in row] for row in reference['H']],
    first_four_J24_boxes_included=True,
    handoff_actual_minus_virtual_bound=str(err),
    handoff_buffer_added='1e-9',event_time_uncertainty=str(dt),
    U_slope_pre=[str(slo_pre.a),str(slo_pre.b)],
    U_slope_post=[str(slo_post.a),str(slo_post.b)],
    both_picard_tubes_passed=True,source_initial=fourth['status'])

def step_uv(data,h,U_on=True,V_on=True,bracket_guard=None):
  t=F(data['t']);root=list(map(F,data['root']));h=F(h)
  noise=list(map(F,data['symbol_radii']));rem=[w.up(z) for z in data['remainder']]
  H=[[w.decode(z) for z in row] for row in data['H']]
  envelope=[sum((w.mag(z)*a for z,a in zip(row,noise)),rem[i]) for i,row in enumerate(H)]
  P,eps=residual_uv(52,t,root,h,U_on,V_on)
  for rr in ('.000001','.00001','.0001','.001'):
   R=F(rr);X=[c.evalpoly(row,I(0,h)).expand(R) for row in P]
   gu,gv,gs=c.guards(X)
   J=J_signed(X,U_on,V_on);A=majorant(J)
   Eflow=c.bound_exp(A,h,envelope,eps)
   valid=all(z<R for z in Eflow) and gs.a>0
   if U_on:valid=valid and (gu.a>0 or (data.get('nsteps',0)==0 and gu_slope(X,True,V_on).a>0))
   else:valid=valid and gu.b<0
   if bracket_guard=='V':valid=valid and (f_rhs(t,t+h,X,U_on,V_on)[3]-f_rhs(t,t+h,X,U_on,V_on)[4]).b<0
   elif V_on:valid=valid and gv.a>0
   else:valid=valid and gv.b<0
   if valid:break
  else:raise AssertionError(('post-fourth UV tube failed',str(t),str(h),float(max(Eflow)),float(gu.a/S),float(gv.a/S),float(gs.a/S)))
  Phi,_,tail=v.exp_bound_signed(J,h,8)
  Hnew=v.mmul(Phi,H)
  forcing=c.bound_exp(A,h,[F(0)]*9,eps)
  rnew=[sum((w.mag(z)*r for z,r in zip(row,rem)),f) for row,f in zip(Phi,forcing)]
  centre=[c.evalpoly(row,I(h)) for row in P]
  root_next,roundoff=c.rational_recenter(centre)
  remnext=[w.up(a+b) for a,b in zip(rnew,roundoff)]
  error=[sum((w.mag(z)*a for z,a in zip(row,noise)),r) for row,r in zip(Hnew,remnext)]
  assert all(e<R for e in error)
  endpoint=[a.expand(e) for a,e in zip(centre,error)]
  gV=endpoint[3]-endpoint[4]-p['Vd']
  return dict(status='J29_UV_VALIDATED_STEP',t=str(t+h),nsteps=data['nsteps']+1,
    root=list(map(str,root_next)),symbol_radii=list(map(str,noise)),
    remainder=list(map(str,remnext)),H=[[w.encode(z) for z in row] for row in Hnew],
    last=dict(max_error=float(max(error)),max_flow_error=float(max(Eflow)),
      R=str(R),gu=[str(gu.a),str(gu.b)],gv=[str(gv.a),str(gv.b)],
      spark=[str(gs.a),str(gs.b)],end_gV=[str(gV.a),str(gV.b)],
      signed_peano_tail=float(tail)))

def advance(data,count,h=F('.005')):
 x=data;rows=[]
 for k in range(count):
  x=step_uv(x,h)
  rows.append(x['last'])
  print(x['nsteps'],float(F(x['t'])),x['last']['max_error'],flush=True)
 x['step_summaries']=rows
 return x

def main():
 ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['handoff','advance','event_v']);ap.add_argument('--fourth');ap.add_argument('--base');ap.add_argument('--input');ap.add_argument('--out',required=True);ap.add_argument('--count',type=int,default=5)
 a=ap.parse_args()
 if a.mode=='handoff':
  z=handoff(json.loads(Path(a.fourth).read_text()),json.loads(Path(a.base).read_text()))
 elif a.mode=='event_v':z=isolate_v_off(json.loads(Path(a.input).read_text()))
 else:z=advance(json.loads(Path(a.input).read_text()),a.count)
 Path(a.out).write_text(json.dumps(z,indent=2)+'\n')
 print('STATUS',z['status'],z.get('t'),flush=True)

def isolate_v_off(data):
 assert data['nsteps']==8
 t=F(data['t']);root=list(map(F,data['root']))
 noise=list(map(F,data['symbol_radii']))
 rem=[w.up(z) for z in data['remainder']]
 H=[[w.decode(z) for z in row] for row in data['H']]
 envelope=[sum((w.mag(z)*a for z,a in zip(row,noise)),rem[i]) for i,row in enumerate(H)]
 cache={}
 def test(h):
  if h not in cache:
   y=step_uv(data,h,bracket_guard='V')
   gg=list(map(int,y['last']['end_gV']))
   cache[h]=(gg,y)
  return cache[h]
 lo,hi=F('.0083'),F('.0084')
 assert test(lo)[0][0]>0 and test(hi)[0][1]<0
 steps=[]
 for k in range(22):
   mid=(lo+hi)/2
   gg,_=test(mid)
   if gg[0]>0:lo=mid;decision='L'
   elif gg[1]<0:hi=mid;decision='R'
   else:decision='ambiguous';steps.append(dict(step=k,decision=decision,mid=str(mid)));break
   steps.append(dict(step=k,decision=decision,mid=str(mid),width=float(hi-lo)))
 assert test(lo)[0][0]>0 and test(hi)[0][1]<0
 h=hi
 P,eps=residual_uv(52,t,root,h,True,True)
 for rr in ('.000001','.00001','.0001'):
  R=F(rr);X=[c.evalpoly(row,I(0,h)).expand(R) for row in P]
  ju,gv,gs=c.guards(X)
  slope=f_rhs(t,t+h,X,True,True)[3]-f_rhs(t,t+h,X,True,True)[4]
  Eflow=c.bound_exp(majorant(J_signed(X,True,True)),h,envelope,eps)
  if all(z<R for z in Eflow) and ju.a>0 and gs.a>0 and slope.b<0:break
 else:raise AssertionError('J29 V OFF event lacks full-time tube')
 state=[c.evalpoly(row,I(lo,hi)).expand(e) for row,e in zip(P,Eflow)]
 originals=json.loads((ROOT/'Artifacts/smith-filsinger/j24_six_hybrid_guard_centres_20261123.json').read_text(),parse_float=F,parse_int=F)['events']
 assert originals[4]['kind']=='diode' and originals[4]['name']=='V'
 members=[z.subset(I(vv-F('.0001'),vv+F('.0001'))) for z,vv in zip(state,originals[4]['x'])]
 return dict(status='J29_FIFTH_DIODE_V_OFF_VALIDATED' if all(members) else 'J29_FIFTH_ROOT_J24_BOX_PENDING',
  event_t_bracket=[str(t+lo),str(t+hi)],width_model_time=str(hi-lo),
  guard_V_left_grid=list(map(str,test(lo)[0])),guard_V_right_grid=list(map(str,test(hi)[0])),
  crossing_slope_signed_decreasing_grid=[str(slope.a),str(slope.b)],
  V_active_U_active_virtual_equations_used_for_root_only=True,
  derivative_strictly_negative=True,
  original_J24_fifth_box_members=members,fifth_J24_full_nine_paid=all(members),
  validated_crossings=5,original_J24_boxes_paid=5 if all(members) else 4,
  event_state_grid=[[str(z.a),str(z.b)] for z in state],
  max_all_time_error=float(max(Eflow)),bisection=steps,
  physical_post_V_off_not_integrated=True,periodic_orbit_proved=False,physical_source_verified=False)

if __name__=="__main__":main()
