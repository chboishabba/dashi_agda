#!/usr/bin/env python3
"""J27 certified nominal event 2: physical diode-V-ON flow to spark OFF.

Replays original J26 first diode event, proves tiny event-time handoff,
then exact outward 9-state Taylor error enclosures and spark saltation gate.
This is NOT a periodic orbit or measured environmental RF energy source.
"""
import json, math
from fractions import Fraction as F
from pathlib import Path
import check_smith_filsinger_j26_first_diode_validated_taylor_20261123 as c
I,S,p=c.I,c.S,c.p

def make_poly_v(N,t0,root):
 states=[[I(x)] for x in root]
 sin0,cos0=c.trig_exact(F('.3')+F('1.1')*t0)
 ss=[sin0];cc=[cos0]
 rho=p['gamma_rad']+p['gamma_internal']
 for n in range(N):
  i,j,u,v,b,q,r,ih,x=states
  ci=lambda X:c.coef(X,n)
  a=-p['R1']*ci(i)
  bb=ci(u)-ci(v)-p['R2']*ci(j)
  di=(p['L2']*a-p['M']*bb)/I('2.64')
  dj=(-p['M']*a+p['L1']*bb)/I('2.64')
  left=-ci(j)+p['k']*ci(q)+p['kh']*ci(ih);jv=(ci(v)-ci(b)-(p['Vd'] if n==0 else I(0)))/p['Rd'];right=ci(j)-jv
  du=(I('1.55')*left+right)/I('1.17')
  dv=(left+I('1.4')*right)/I('1.17')
  db=(jv-p['Gbleed']*ci(b)-ci(ih))/p['Cb']
  dq=p['omega']*ci(r)-rho*ci(q)-p['k']*ci(u)/I(2)+c.j25.RAD*p['source_amp']*cc[n]
  dr=-p['omega']*ci(q)-rho*ci(r)-c.j25.RAD*p['source_amp']*ss[n]
  dih=(ci(b)-ci(x)-(p['Rcoil']+p['Rgap'])*ci(ih)-p['kh']*ci(u))/p['Lh']
  D=[];inv=[]
  for k in range(n+1):
   D.append((I(1) if k==0 else I(0))+I('1.5')*c.coeff(x,x,k))
   if k==0:inv.append(I(1)/D[0])
   else:inv.append(-sum((D[j]*inv[k-j] for j in range(1,k+1)),I(0))/D[0])
  dc=sum(((c.coef(ih,k)-p['Gload']*c.coef(x,k))*inv[n-k] for k in range(n+1)),I(0))/p['Ch']
  for s,vv in zip(states,[di,dj,du,dv,db,dq,dr,dih,dc]):s.append(vv/I(n+1))
  ss.append(p['omega']*cc[n]/I(n+1)); cc.append(-p['omega']*ss[n]/I(n+1))
 return states,ss,cc

def coeff_series_rhs_v(P,SS,CC,N):
    i,j,u,v,b,q,r,ih,cap=P
    out=[]
    for n in range(N+1):
        ci=lambda x:c.coef(x,n)
        a=-p['R1']*ci(i);bb=ci(u)-ci(v)-p['R2']*ci(j)
        left=-ci(j)+p['k']*ci(q)+p['kh']*ci(ih);jv=(ci(v)-ci(b)-(p['Vd'] if n==0 else I(0)))/p['Rd'];right=ci(j)-jv
        vals=[(p['L2']*a-p['M']*bb)/I('2.64'),(-p['M']*a+p['L1']*bb)/I('2.64'),
           (I('1.55')*left+right)/I('1.17'),(left+I('1.4')*right)/I('1.17'),
           (jv-p['Gbleed']*ci(b)-ci(ih))/p['Cb'],
           p['omega']*ci(r)-(p['gamma_rad']+p['gamma_internal'])*ci(q)-p['k']*ci(u)/I(2)+c.j25.RAD*p['source_amp']*c.coef(CC,n),
           -p['omega']*ci(q)-(p['gamma_rad']+p['gamma_internal'])*ci(r)-c.j25.RAD*p['source_amp']*c.coef(SS,n),
           (ci(b)-ci(cap)-(p['Rcoil']+p['Rgap'])*ci(ih)-p['kh']*ci(u))/p['Lh']]
        out.append(vals)
    return out

def get_A_v(tube):
    p=c.p; cap=tube[8];ih=tube[7]
    z=I(0); J=[[z for _ in range(9)] for _ in range(9)]
    J[0][0]=-p['R1']*I('1.5')/I('2.64')
    J[0][1]=p['M']*p['R2']/I('2.64')
    J[0][2]=-p['M']/I('2.64'); J[0][3]=p['M']/I('2.64')
    J[1][0]=p['M']*p['R1']/I('2.64')
    J[1][1]=-p['L1']*p['R2']/I('2.64')
    J[1][2]=p['L1']/I('2.64');J[1][3]=-p['L1']/I('2.64')
    J[2][1]=-I('.55')/I('1.17')
    J[2][5]=I('1.55')*p['k']/I('1.17')
    J[2][7]=I('1.55')*p['kh']/I('1.17')
    J[3][1]=I('.4')/I('1.17')
    J[3][5]=p['k']/I('1.17'); J[3][7]=p['kh']/I('1.17')
    J[4][4]=-p['Gbleed']/p['Cb'];J[4][7]=-I(1)/p['Cb']
    J[5][2]=-p['k']/I(2)
    J[5][5]=-p['gamma_rad']-p['gamma_internal'];J[5][6]=p['omega']
    J[6][5]=-p['omega'];J[6][6]=-p['gamma_rad']-p['gamma_internal']
    J[7][2]=-p['kh']/p['Lh'];J[7][4]=I(1)/p['Lh']
    J[7][7]=-(p['Rcoil']+p['Rgap'])/p['Lh'];J[7][8]=-I(1)/p['Lh']
    g=I(1)+I('1.5')*cap**2
    J[8][7]=I(1)/(p['Ch']*g)
    J[8][8]=-p['Gload']/(p['Ch']*g)-(ih-p['Gload']*cap)*I(3)*cap/(p['Ch']*g**2)
    # Explicit V-diode active Jacobian for jv=(v-b-Vd)/Rd.
    jiv=I(1)/p['Rd']
    J[2][3]=-jiv/I('1.17');J[2][4]=jiv/I('1.17')
    J[3][3]=-I('1.4')*jiv/I('1.17');J[3][4]=I('1.4')*jiv/I('1.17')
    J[4][3]=jiv/p['Cb'];J[4][4]=-(p['Gbleed']+jiv)/p['Cb']
    return [[F(c.supabs(x),S) for x in row] for row in J]

def residual_v(N,t0,root,h):
 P,SS,CC=make_poly_v(N,t0,root)
 rhs=coeff_series_rhs_v(P,SS,CC,N)
 polys=[]
 for j in range(8):
  res=[]
  for n in range(N+1):
   der=P[j][n+1]*I(n+1) if n+1<len(P[j]) else I(0)
   res.append(der-rhs[n][j])
  polys.append(res)
 i,j,u,v,b,q,r,ih,cap=P
 D=c.mul(cap,cap)
 D=[I('1.5')*x+(I(1) if k==0 else I(0)) for k,x in enumerate(D)]
 cd=[x*I(k+1) for k,x in enumerate(cap[1:])]
 res=c.mul(D,cd)
 for k in range(len(res)):res[k]=p['Ch']*res[k]-(c.coef(ih,k)-p['Gload']*c.coef(cap,k))
 bound=[c.evalabs(x,I(h)) for x in polys]
 bound.append(c.j25.ceil_div(c.evalabs(res,I(h))*S,p['Ch'].a))
 forc=F('.21')*F('1.1')**N*h**N/F(math.factorial(N))
 tail=I(0,forc).b
 bound[5]+=tail;bound[6]+=tail
 return P,[F(x,S) for x in bound]

def gV_slope_active(tube):
    i,j,u,v,b,q,r,ih,x=tube
    jv=(v-b-p['Vd'])/p['Rd']
    left=-j+p['k']*q+p['kh']*ih
    right=j-jv
    dv=(left+I('1.4')*right)/I('1.17')
    db=(jv-p['Gbleed']*b-ih)/p['Cb']
    return dv-db

def spark_minus_slope(tube):
    i,j,u,v,b,q,r,ih,x=tube
    jv=(v-b-p['Vd'])/p['Rd']
    return -(jv-p['Gbleed']*b-ih)/p['Cb']

def step_v(t0,h,root,delta,R,N=52,spark_bracket=False,early_on_slope=False):
    t0=F(t0);h=F(h);R=F(R)
    P,eps=residual_v(N,t0,root,h)
    tube=[c.evalpoly(row,I(0,h)).expand(R) for row in P]
    gu,gv,gs=c.guards(tube)
    E=c.bound_exp(get_A_v(tube),h,delta,eps)
    accepted=all(e<R for e in E) and gu.b<0
    if spark_bracket:accepted=accepted and spark_minus_slope(tube).a>0
    else:accepted=accepted and gs.a>0
    if early_on_slope:accepted=accepted and gV_slope_active(tube).a>0
    else:accepted=accepted and gv.a>0
    endpoint=[c.evalpoly(row,I(h)) for row in P]
    endpoint_box=[z.expand(e) for z,e in zip(endpoint,E)]
    root_n,delta_n=c.rational_recenter(endpoint_box)
    eg=c.guards(endpoint_box)
    return dict(valid=accepted,t0=str(t0),t1=str(t0+h),
       spark_guard=[str(gs.a),str(gs.b)],
       V_guard=[str(gv.a),str(gv.b)],U_guard=[str(gu.a),str(gu.b)],
       spark_endpoint=[str(eg[2].a),str(eg[2].b)],
       signed_spark_slope=[str(spark_minus_slope(tube).a),str(spark_minus_slope(tube).b)],
       signed_V_slope=[str(gV_slope_active(tube).a),str(gV_slope_active(tube).b)],
       max_error=float(max(E)),radius=str(R)),root_n,delta_n

def run():
    root=[F(x) for x in c.j25.ROOT];delta=[F(0)]*9;t=F(0)
    original_segments=[]
    for h in [F('.1')]*33+[F('.02')]*4:
        chosen=None
        for rr in ('.000000001','.00000001','.0000001','.000001','.00001'):
            row,nxt,dn=c.step(t,h,root,delta,N=52,R=F(rr))
            if row['isinc'] and row['guards']:chosen=row,nxt,dn;break
        assert chosen is not None
        row,root,delta=chosen;original_segments.append(row);t+=h
    assert t==F('3.38')
    root0=root[:];d0=delta[:]
    first_virtual,root,delta=c.step(t,F('.009367010'),root,delta,N=52,R=F('.00000001'),accept_if_slope=True)
    assert first_virtual['isinc'] and first_virtual['guards'] and first_virtual['gV_end'][0]>0

    # Repeat both original J26 endpoint signs and nine-coordinate J24 inclusion,
    # reusing the already verified exact t=3.38 state instead of rerunning it.
    first_left=c.step(t,F('.009367008'),root0,d0,N=52,R=F('.00000001'),accept_if_slope=True)[0]
    assert first_left['isinc'] and first_left['guards'] and first_left['gV_end'][1]<0
    assert first_virtual['gV_slope_whole'][0]>0
    orig_events=json.loads((Path(__file__).resolve().parents[1]/'Artifacts/smith-filsinger/j24_six_hybrid_guard_centres_20261123.json').read_text(),parse_float=F,parse_int=F)['events']
    Pfirst,epsfirst=c.residual(52,t,root0,F('.009367010'))
    tf=[c.evalpoly(row,I(0,F('.009367010'))).expand(F('.00000001')) for row in Pfirst]
    Ef=c.bound_exp(c.get_A(tf),F('.009367010'),d0,epsfirst)
    first_state=[c.evalpoly(row,I(F('.009367008'),F('.009367010'))).expand(e) for row,e in zip(Pfirst,Ef)]
    assert all(x.subset(I(v-F('.0001'),v+F('.0001'))) for x,v in zip(first_state,orig_events[0]['x']))

    # Rigorous event-time handoff from virtual inactive V to the actual V-on
    # field over at most 2e-9 time: instantaneous state is continuous.
    h_to_right=F('.009367010')
    Pv,epv=c.residual(52,t,root0,h_to_right)
    virtual_tube=[c.evalpoly(row,I(0,h_to_right)).expand(F('.000000011')) for row in Pv]
    A=get_A_v(virtual_tube)
    assert max(map(sum,A))<100
    assert gV_slope_active(virtual_tube).a>0
    # positive virtual V guard after unique crossing, upper slope < 1/2
    assert first_virtual['gV_slope_whole'][1]<F(1,2)
    # max |f_active(v)-f_inactive(v)| < 13e-9;
    # exp(100*2e-9) <= 1/(1-2e-7)<2.
    dt=F(2,10**9)
    assert F(100)*dt < F(1,2)
    exp_upper=1/(1-F(100)*dt)
    handoff_error=dt*F(13,10**9)*exp_upper
    assert handoff_error < F(1,10**15)
    delta=[d+F(1,10**15) for d in delta]
    t=F('3.389367010')
    # V-on (physical) from the right-hand event-time boundary.
    steps=[F('.002')]+[F('.01')]*9+[F('.002'),F('.005'),F('.002')]
    rows=[]
    for idx,h in enumerate(steps):
        chosen=None
        for radius in ('.000000001','.00000001','.0000001','.000001','.00001'):
            row,nxt,dn=step_v(t,h,root,delta,F(radius),early_on_slope=(idx==0))
            if row['valid']:chosen=row,nxt,dn;break
        assert chosen is not None,(idx,str(t),row)
        row,root,delta=chosen;t+=h;rows.append(row)
    assert t==F('3.490367010') and len(rows)==13
    h_left=F('.00092568');h_right=F('.00092574')
    left=step_v(t,h_left,root,delta,F('.0000001'),spark_bracket=True)[0]
    right=step_v(t,h_right,root,delta,F('.0000001'),spark_bracket=True)[0]
    assert left['valid'] and right['valid']
    assert int(left['spark_endpoint'][0])>0 and int(right['spark_endpoint'][1])<0
    assert int(right['signed_spark_slope'][0])>0

    P,eps=residual_v(52,t,root,h_right)
    tube=[c.evalpoly(row,I(0,h_right)).expand(F('.0000001')) for row in P]
    E=c.bound_exp(get_A_v(tube),h_right,delta,eps)
    event_state=[c.evalpoly(row,I(h_left,h_right)).expand(e) for row,e in zip(P,E)]
    events=json.loads((Path(__file__).resolve().parents[1]/'Artifacts/smith-filsinger/j24_six_hybrid_guard_centres_20261123.json').read_text(),parse_float=F,parse_int=F)['events']
    assert events[1]['kind']=='spark' and events[1]['name']=='off'
    original_box=[I(v-F('.0001'),v+F('.0001')) for v in events[1]['x']]
    assert all(x.subset(b) for x,b in zip(event_state,original_box))
    # Rank-one spark saltation det is post_bank_slope / pre_bank_slope.
    v,b,ih=event_state[3],event_state[4],event_state[7]
    jv=(v-b-p['Vd'])/p['Rd']
    pre=(jv-p['Gbleed']*b-ih)/p['Cb']
    post=(jv-p['Gbleed']*b)/p['Cb']
    assert pre.b<0 and post.a>0
    determinant=post/pre
    assert determinant.b<0
    return dict(status='J27_PASS_NOMINAL_TWO_EVENTS_AND_J24_BOXES_2_OF_6',
      original_J26_first_event_replayed=True,
      diode_V_switch_interval=['3.389367008','3.389367010'],
      diode_handoff_error_upper=str(handoff_error),
      original_J24_first_event_box_included=True,
      physical_V_active_guard_free_segments=len(rows),
      physical_V_active_flow_through=str(t),
      spark_OFF_time_bracket=[str(t+h_left),str(t+h_right)],
      spark_crossing_signed_slope_grid=right['signed_spark_slope'],
      spark_left_guard_grid=left['spark_endpoint'],
      spark_right_guard_grid=right['spark_endpoint'],
      original_J24_spark_OFF_event_box_all_9_included=True,
      spark_OFF_saltation_determinant_grid=[str(determinant.a),str(determinant.b)],
      spark_OFF_saltation_orientation_reversing=True,
      event_state_grid=[[str(x.a),str(x.b)] for x in event_state],
      active_diodes_U_false_V_true=True,
      physical_after_spark_OFF_not_integrated=True,
      exact_full_tau_periodic_orbit_proved=False,uniform_five_parameter_family_proved=False,
      source_is_unmeasured_synthetic=True,github_actions_CI_run=False)

if __name__=='__main__':
 print(json.dumps(run(),indent=2,sort_keys=True))
