#!/usr/bin/env python3
"""J28 nominal interval OFF-mode handoff and spark-ON isolation.

Uses J27 exact interval witness for the uncertain spark-OFF event, then
integrates the actual V-active, U-inactive, spark-OFF nine-state equations.
Source is synthetic, fixed rational initial state, not a periodic-orbit proof.
"""
import json, math
from pathlib import Path
from fractions import Fraction as F
import check_smith_filsinger_j27_second_spark_off_validated_20261123 as j27
c=j27.c; I,S,p = c.I,c.S,c.p

ON_RIGHT=F('3.49129275')

def mode_rhs_poly(P,SS,CC,n,chi):
    i,j,u,v,b,q,r,ih,cap=P
    ci=lambda x:c.coef(x,n)
    a=-p['R1']*ci(i); bb=ci(u)-ci(v)-p['R2']*ci(j)
    jv=(ci(v)-ci(b)-(p['Vd'] if n==0 else I(0)))/p['Rd']
    left=-ci(j)+p['k']*ci(q)+p['kh']*ci(ih)
    right=ci(j)-jv
    return [
        (p['L2']*a-p['M']*bb)/I('2.64'),
        (-p['M']*a+p['L1']*bb)/I('2.64'),
        (I('1.55')*left+right)/I('1.17'),
        (left+I('1.4')*right)/I('1.17'),
        (jv-p['Gbleed']*ci(b)-I(chi)*ci(ih))/p['Cb'],
        p['omega']*ci(r)-(p['gamma_rad']+p['gamma_internal'])*ci(q)-p['k']*ci(u)/I(2)+c.j25.RAD*p['source_amp']*c.coef(CC,n),
        -p['omega']*ci(q)-(p['gamma_rad']+p['gamma_internal'])*ci(r)-c.j25.RAD*p['source_amp']*c.coef(SS,n),
        (I(chi)*ci(b)-ci(cap)-(p['Rcoil']+I(chi)*p['Rgap'])*ci(ih)-p['kh']*ci(u))/p['Lh']]

def make_poly_mode(N,t0,root,chi=0):
    P=[[I(x)] for x in root]
    ss0,cc0=c.trig_exact(F('.3')+F('1.1')*t0)
    SS=[ss0];CC=[cc0]
    for n in range(N):
        d=mode_rhs_poly(P,SS,CC,n,chi)
        cap=P[8]
        D=[];inv=[]
        for k in range(n+1):
            D.append((I(1) if k==0 else I(0))+I('1.5')*c.coeff(cap,cap,k))
            if k==0:inv.append(I(1)/D[0])
            else:inv.append(-sum((D[m]*inv[k-m] for m in range(1,k+1)),I(0))/D[0])
        dc=sum(((c.coef(P[7],m)-p['Gload']*c.coef(cap,m))*inv[n-m] for m in range(n+1)),I(0))/p['Ch']
        for seq,v in zip(P,d+[dc]):seq.append(v/I(n+1))
        SS.append(p['omega']*CC[n]/I(n+1))
        CC.append(-p['omega']*SS[n]/I(n+1))
    return P,SS,CC

def residual_mode(N,t0,root,h,chi=0):
    P,SS,CC=make_poly_mode(N,t0,root,chi)
    rhs=[mode_rhs_poly(P,SS,CC,n,chi) for n in range(N+1)]
    polys=[]
    for j in range(8):
        v=[]
        for n in range(N+1):
            derivative=(P[j][n+1]*I(n+1)) if n+1<len(P[j]) else I(0)
            v.append(derivative-rhs[n][j])
        polys.append(v)
    cap=P[8];D=c.mul(cap,cap)
    D=[I('1.5')*x+(I(1) if k==0 else I(0)) for k,x in enumerate(D)]
    cd=[x*I(k+1) for k,x in enumerate(cap[1:])]
    res=c.mul(D,cd)
    for k in range(len(res)):
        res[k]=p['Ch']*res[k]-(c.coef(P[7],k)-p['Gload']*c.coef(cap,k))
    bounds=[c.evalabs(v,I(h)) for v in polys]
    bounds.append(c.j25.ceil_div(c.evalabs(res,I(h))*S,p['Ch'].a))
    tail=I(0,F('.21')*F('1.1')**N*F(h)**N/F(math.factorial(N))).b
    bounds[5]+=tail;bounds[6]+=tail
    return P,[F(v,S) for v in bounds]

def jacobian_mode(tube,chi=0):
    A=j27.get_A_v(tube)
    # Bounds are already exact nonnegative magnitudes. Alter only terms
    # depending on spark mode chi; all other branch terms remain unchanged.
    A[4][7]=F(chi)/F(p['Cb'].a,S) # equivalent to chi/Cb, exact rational interval parameter
    A[7][4]=F(chi)/F(p['Lh'].a,S)
    A[7][7]=F(p['Rcoil'].b,S)/F(p['Lh'].a,S) if not chi else (F(p['Rcoil'].b+p['Rgap'].b,S)/F(p['Lh'].a,S))
    return A

def trig_interval(tlo,thi):
    phase=F('.3')+F('1.1')*F(tlo)
    si,co=c.trig_exact(phase)
    inc=I(0,F('1.1')*(F(thi)-F(tlo)))
    return si.expand(F(inc.b,S)),co.expand(F(inc.b,S))

def interval_rhs_off(tlo,thi,X):
    i,j,u,v,b,q,r,ih,cap=X
    si,co=trig_interval(tlo,thi)
    jv=(v-b-p['Vd'])/p['Rd']
    a=-p['R1']*i;bb=u-v-p['R2']*j
    left=-j+p['k']*q+p['kh']*ih;right=j-jv
    gam=p['gamma_rad']+p['gamma_internal']
    return [
        (p['L2']*a-p['M']*bb)/I('2.64'),
        (-p['M']*a+p['L1']*bb)/I('2.64'),
        (I('1.55')*left+right)/I('1.17'),
        (left+I('1.4')*right)/I('1.17'),
        (jv-p['Gbleed']*b)/p['Cb'],
        p['omega']*r-gam*q-p['k']*u/I(2)+c.j25.RAD*p['source_amp']*co,
        -p['omega']*q-gam*r-c.j25.RAD*p['source_amp']*si,
        (-cap-p['Rcoil']*ih-p['kh']*u)/p['Lh'],
        (ih-p['Gload']*cap)/(p['Ch']*(I(1)+I('1.5')*cap**2))]

def spark_slope_off(X):
    _,_,_,v,b,_,_,ih,_=X
    jv=(v-b-p['Vd'])/p['Rd']
    return (jv-p['Gbleed']*b)/p['Cb']

def step_off(t,h,root,delta,R,N=52,bracket=False):
    t=F(t);h=F(h);R=F(R)
    P,eps=residual_mode(N,t,root,h)
    X=[c.evalpoly(row,I(0,h)).expand(R) for row in P]
    gu,gv,_=c.guards(X)
    gON=X[4]-p['Von']
    E=c.bound_exp(jacobian_mode(X),h,delta,eps)
    valid=all(e<R for e in E) and gu.b<0 and gv.a>0
    slope=spark_slope_off(X)
    if bracket:valid=valid and slope.a>0
    else:valid=valid and gON.b<0
    endpoint=[c.evalpoly(row,I(h)) for row in P]
    box=[z.expand(e) for z,e in zip(endpoint,E)]
    return dict(valid=valid,t0=str(t),t1=str(t+h),
       gON_whole=[str(gON.a),str(gON.b)],
       gON_end=[str((box[4]-p['Von']).a),str((box[4]-p['Von']).b)],
       V_whole=[str(gv.a),str(gv.b)],U_whole=[str(gu.a),str(gu.b)],
       signed_ON_slope=[str(slope.a),str(slope.b)],
       max_error=float(max(E)),radius=str(R)),*c.rational_recenter(box)

def run():
    j27_receipt=j27.run()   # preserve source-first original 2/6 gates
    assert j27_receipt['original_J24_spark_OFF_event_box_all_9_included']
    tleft=F('3.49129269');tright=F('3.49129275')
    state0=[I(int(a),int(b),raw=True) for a,b in j27_receipt['event_state_grid']]
    dt=tright-tleft
    # Bound true physical OFF solution from uncertain event state and time
    # to the fixed right endpoint using Picard self-inclusion.
    radius=F('.00001')
    tube=[x.expand(radius) for x in state0]
    rhs=interval_rhs_off(tleft,tright,tube)
    covers=[x+I(0,dt)*v for x,v in zip(state0,rhs)]
    assert all(e.subset(b) for e,b in zip(covers,tube))
    assert (tube[2]-tube[4]-p['Vd']).b<0
    assert (tube[3]-tube[4]-p['Vd']).a>0
    assert (tube[4]-p['Von']).b<0
    A=jacobian_mode(tube)
    L=max(map(sum,A))
    assert L*dt<F(1,2)
    root,delta=c.rational_recenter(covers)
    t=tright
    accepted=[]
    steps=[F('.005')]*4+[F('.002')]
    for idx,h in enumerate(steps):
        found=None
        for rr in ('.0000001','.000001','.00001','.0001'):
            row,nxt,delta_next=step_off(t,h,root,delta,F(rr))
            if row['valid']:
                found=row,nxt,delta_next;break
        assert found is not None,(idx,str(t),row)
        row,root,delta=found;t+=h;accepted.append(row)
    assert t==F('3.51329275')
    hleft=F('.0020475');hright=F('.0020482')
    left=step_off(t,hleft,root,delta,F('.000001'),bracket=True)[0]
    right=step_off(t,hright,root,delta,F('.000001'),bracket=True)[0]
    assert left['valid'] and right['valid']
    assert int(left['gON_end'][1])<0 and int(right['gON_end'][0])>0
    assert int(right['signed_ON_slope'][0])>0
    # Entire uncertain third event-time interval and full nine-state error.
    P,eps=residual_mode(52,t,root,hright,chi=0)
    tube=[c.evalpoly(row,I(0,hright)).expand(F('.000001')) for row in P]
    E=c.bound_exp(jacobian_mode(tube),hright,delta,eps)
    third_state=[c.evalpoly(row,I(hleft,hright)).expand(e) for row,e in zip(P,E)]
    original=json.loads((Path(__file__).resolve().parents[1]/'Artifacts/smith-filsinger/j24_six_hybrid_guard_centres_20261123.json').read_text(),parse_float=F,parse_int=F)['events']
    assert original[2]['kind']=='spark' and original[2]['name']=='on'
    box=[I(x-F('.0001'),x+F('.0001')) for x in original[2]['x']]
    assert all(x.subset(y) for x,y in zip(third_state,box))
    assert (third_state[2]-third_state[4]-p['Vd']).b<0
    assert (third_state[3]-third_state[4]-p['Vd']).a>0
    # Spark OFF -> ON saltation: det(S) = bank_slope_after / before.
    _,_,_,v,b,_,_,ih,_=third_state
    jv=(v-b-p['Vd'])/p['Rd']
    pre=(jv-p['Gbleed']*b)/p['Cb']
    post=(jv-p['Gbleed']*b-ih)/p['Cb']
    assert pre.a>0 and post.b<0
    determinant=post/pre
    assert determinant.b<0
    return dict(status='J28_PASS_NOMINAL_THREE_EVENTS_J24_BOXES_3_OF_6',
       previous_J27_first_two_events=j27_receipt['status'],
       spark_OFF_time_bracket=[str(tleft),str(tright)],
       uncertain_OFF_handoff_width=str(dt),
       handoff_picard_inclusion=True,handoff_L_upper=str(L),
       handoff_max_state_width=float(max(x.width() for x in covers)),
       post_OFF_guard_free_segments=len(accepted),post_OFF_time=str(t),
       spark_ON_time_bracket=[str(t+hleft),str(t+hright)],
       third_event_ON_slope_grid=right['signed_ON_slope'],
       spark_ON_left_guard_grid=left['gON_end'],
       spark_ON_right_guard_grid=right['gON_end'],
       third_J24_spark_ON_box_included_all_nine=True,
       third_event_state_grid=[[str(x.a),str(x.b)] for x in third_state],
       spark_ON_saltation_determinant_grid=[str(determinant.a),str(determinant.b)],
       post_ON_flow_not_integrated=True,
       post_OFF_guard_rows=accepted,
       exact_periodic_orbit_proved=False,environmental_power_verified=False,
       original_five_parameter_uniform_flow_proved=False,github_actions_or_ci_run=False)

if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
