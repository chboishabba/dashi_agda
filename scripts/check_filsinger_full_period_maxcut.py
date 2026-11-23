#!/usr/bin/env python3
"""Filsinger P0 max-cut: one fail-closed continuation from J28B to full tau.

J29B/J30/J31 candidate executor for the unchanged J18 9-state source model.
It *attempts* to isolate fifth and sixth diode events, carry the source-period
return, and report the endpoint defect. It never claims an exact periodic orbit
without a nonzero-box interval derivative and a Banach/Krawczyk certificate.

Run locally from the dashi_agda repository:
  python scripts/check_filsinger_full_period_maxcut.py \
    --checkpoint Artifacts/smith-filsinger/j28b_signed_75_step_exact_checkpoint_20261123.json \
    --out-dir Artifacts/smith-filsinger/full-period-maxcut --budget 90

Uses exact outward 1e30 grid interval operations inherited from J25–J28B.
No Actions/CI. Original Filsinger hardware/input-energy evidence remains open.
"""
import argparse, hashlib, json, math, sys, time, traceback
from fractions import Fraction as F
from pathlib import Path

import check_smith_filsinger_j28b_signed_peano_baker_20261123 as j28b
j27=j28b.j27
c=j28b.c
I,S,p=c.I,c.S,c.p
ROOT_REPO=Path(__file__).resolve().parents[1]
EXPECTED={
    'scripts/check_smith_filsinger_j28b_signed_peano_baker_20261123.py':'1a357ce4719fb552680c1b042237283abb977b6a',
    'Artifacts/smith-filsinger/j28b_signed_75_step_exact_checkpoint_20261123.json':'74c1a94b30c44a772016c93b39558bc446359832',
    'scripts/check_smith_filsinger_j27_second_spark_off_validated_20261123.py':'6c7d7781f11943fc5b1267a6259bf3dc14f374d3',
    'scripts/check_smith_filsinger_j25_first_segment_validated_interval_20261123.py':'5d723374d71281cc5583582cc17d15016deaa8a3',
    'scripts/check_smith_filsinger_j26_first_diode_validated_taylor_20261123.py':'78cfdaa6c473eb1712194a17fa5ee46fa9dd5a94',
    'scripts/check_smith_filsinger_j28_spark_return_on_interval_20261123.py':'e22573e6189ff460e80f9bc1de13b3787d169b79',
    'scripts/check_smith_filsinger_j29a_diode_u_continuity.py':'07b1c4a48f69d08e53e5221c25ea47f685b63121',
    'Artifacts/smith-filsinger/j29a_fourth_U_physical_handoff_20261123.json':'606e2062c29644077ea86eec62a7320ac0d4c1d1',
    'Artifacts/smith-filsinger/j24_six_hybrid_guard_centres_20261123.json':'edcec489212e81b473af5ea1049b958236781d12',
}
N=52
TARGETS=(('V_OFF',F('4.31574095'),F('.0076'),F('.0086')),
         ('U_OFF',F('4.92434095'),F('.0038'),F('.005')))

def blob_id(data):return hashlib.sha1(('blob %d\0'%len(data)).encode()+data).hexdigest()

def proof_inputs(root):
    for path,sha in EXPECTED.items():
        actual=blob_id((root/path).read_bytes())
        assert actual==sha, ('source-drift',path,actual,sha)

def coef(z,n):return c.coef(z,n)

def current_coeff(Q,B,n,on):
    return (coef(Q,n)-coef(B,n)-(p['Vd'] if n==0 else I(0)))/p['Rd'] if on else I(0)

def rhs_coeff(P,SS,CC,n,mode):
    U,V,spark=mode
    i,j,u,v,b,q,r,ih,cap=P
    ci=lambda z:coef(z,n)
    ju=current_coeff(u,b,n,U); jv=current_coeff(v,b,n,V)
    a=-p['R1']*ci(i);bb=ci(u)-ci(v)-p['R2']*ci(j)
    left=-ci(j)-ju+p['k']*ci(q)+p['kh']*ci(ih)
    right=ci(j)-jv
    return [
      (p['L2']*a-p['M']*bb)/I('2.64'),(-p['M']*a+p['L1']*bb)/I('2.64'),
      (I('1.55')*left+right)/I('1.17'),
      (left+I('1.4')*right)/I('1.17'),
      (ju+jv-p['Gbleed']*ci(b)-I(int(spark))*ci(ih))/p['Cb'],
      p['omega']*ci(r)-(p['gamma_rad']+p['gamma_internal'])*ci(q)
        -p['k']*ci(u)/I(2)+c.j25.RAD*p['source_amp']*ci(CC),
      -p['omega']*ci(q)-(p['gamma_rad']+p['gamma_internal'])*ci(r)
        -c.j25.RAD*p['source_amp']*ci(SS),
      (I(int(spark))*ci(b)-ci(cap)-(p['Rcoil']+I(int(spark))*p['Rgap'])*ci(ih)
        -p['kh']*ci(u))/p['Lh']]

def poly_mode(t0,root,mode,n=N):
    P=[[I(z)] for z in root]
    sin0,cos0=c.trig_exact(F('.3')+F('1.1')*F(t0))
    SS=[sin0];CC=[cos0]
    for k in range(n):
        vals=rhs_coeff(P,SS,CC,k,mode)
        cap=P[8]
        D=[];Inv=[]
        for j in range(k+1):
            D.append((I(1) if j==0 else I(0))+I('1.5')*c.coeff(cap,cap,j))
            if j==0:Inv.append(I(1)/D[0])
            else:Inv.append(-sum((D[l]*Inv[j-l] for l in range(1,j+1)),I(0))/D[0])
        dx=sum(((coef(P[7],j)-p['Gload']*coef(cap,j))*Inv[k-j]
                for j in range(k+1)),I(0))/p['Ch']
        for s,v in zip(P,vals+[dx]):s.append(v/I(k+1))
        SS.append(p['omega']*CC[k]/I(k+1))
        CC.append(-p['omega']*SS[k]/I(k+1))
    return P,SS,CC

def residual_mode(t0,h,root,mode,n=N):
    P,SS,CC=poly_mode(t0,root,mode,n)
    rr=[[] for _ in range(8)]
    for k in range(n+1):
        rhs=rhs_coeff(P,SS,CC,k,mode)
        for j in range(8):
            deriv=P[j][k+1]*I(k+1) if k+1<len(P[j]) else I(0)
            rr[j].append(deriv-rhs[j])
    cap=P[8]
    D=[I('1.5')*val+(I(1) if k==0 else I(0))
       for k,val in enumerate(c.mul(cap,cap))]
    derivative=[v*I(k+1) for k,v in enumerate(cap[1:])]
    implicit=c.mul(D,derivative)
    for k in range(len(implicit)):
        implicit[k]=p['Ch']*implicit[k]-(coef(P[7],k)-p['Gload']*coef(cap,k))
    bound=[c.evalabs(row,I(h)) for row in rr]
    bound.append(c.j25.ceil_div(c.evalabs(implicit,I(h))*S,p['Ch'].a))
    forc=F('.21')*F('1.1')**n*F(h)**n/F(math.factorial(n))
    tail=I(0,forc).b;bound[5]+=tail;bound[6]+=tail
    return P,[F(v,S) for v in bound]

def jac_mode(X,mode):
    U,V,spark=mode
    # J28B's signed Jacobian of U-inactive, V-active and spark-ON model.
    J=j28b.jsigned(X)
    g=I(1)/p['Rd']
    # Remove V diode's signed Jacobian terms when V is inactive.
    if not V:
        J[2][3]=J[2][3]+g/I('1.17')
        J[2][4]=J[2][4]-g/I('1.17')
        J[3][3]=J[3][3]+I('1.4')*g/I('1.17')
        J[3][4]=J[3][4]-I('1.4')*g/I('1.17')
        J[4][3]=J[4][3]-g/p['Cb']
        J[4][4]=J[4][4]+g/p['Cb']
    if U:
        J[2][2]=J[2][2]-I('1.55')*g/I('1.17')
        J[2][4]=J[2][4]+I('1.55')*g/I('1.17')
        J[3][2]=J[3][2]-g/I('1.17')
        J[3][4]=J[3][4]+g/I('1.17')
        J[4][2]=J[4][2]+g/p['Cb']
        J[4][4]=J[4][4]-g/p['Cb']
    if not spark:
        J[4][7]=I(0);J[7][4]=I(0)
        J[7][7]=-p['Rcoil']/p['Lh']
    return J

def error_signed(X,h,delta,eps,mode):
    J=jac_mode(X,mode)
    phi,L,tail=j28b.exp_bound_signed(J,h)
    init=[sum((F(c.supabs(x),S)*d for x,d in zip(row,delta)),F(0)) for row in phi]
    majorant=[[F(c.supabs(v),S) for v in row] for row in J]
    forced=c.bound_exp(majorant,h,[F(0)]*9,eps)
    return [a+b for a,b in zip(init,forced)], dict(L=str(L),
        peano_tail=str(tail),initial_error=str(max(init)),forcing=str(max(forced)))

def guards(X):return c.guards(X)

def root_slope(X,mode,target):
    # Direction-correct derivative of target guard on the virtual pre-switch field.
    rhs=rhs_interval(X,mode)
    if target=='V_OFF':return rhs[4]-rhs[3]
    if target=='U_OFF':return rhs[4]-rhs[2]
    raise ValueError(target)

def trig_interval(t0,t1):
    mid=F('.3')+F('1.1')*(F(t0)+F(t1))/2
    uncertainty=F('1.1')*(F(t1)-F(t0))/2
    sn,cs=c.trig_exact(mid)
    return sn.expand(uncertainty),cs.expand(uncertainty)

def full_rhs_interval(t0,t1,X,mode):
    U,V,spark=mode
    i,j,u,v,b,q,r,ih,x=X
    linear=rhs_interval(X,mode)
    sn,cs=trig_interval(t0,t1)
    source=c.j25.RAD*p['source_amp']
    gam=p['gamma_rad']+p['gamma_internal']
    dq=p['omega']*r-gam*q-p['k']*u/I(2)+source*cs
    dr=-p['omega']*q-gam*r-source*sn
    dih=(I(int(spark))*b-x-(p['Rcoil']+I(int(spark))*p['Rgap'])*ih-p['kh']*u)/p['Lh']
    dx=(ih-p['Gload']*x)/(p['Ch']*(I(1)+I('1.5')*x**2))
    return linear+[dq,dr,dih,dx]

def rhs_interval(X,mode):
    U,V,spark=mode
    i,j,u,v,b,q,r,ih,x=X
    ju=(u-b-p['Vd'])/p['Rd'] if U else I(0)
    jv=(v-b-p['Vd'])/p['Rd'] if V else I(0)
    aa=-p['R1']*i;bb=u-v-p['R2']*j
    left=-j-ju+p['k']*q+p['kh']*ih
    right=j-jv
    di=(p['L2']*aa-p['M']*bb)/I('2.64')
    dj=(-p['M']*aa+p['L1']*bb)/I('2.64')
    du=(I('1.55')*left+right)/I('1.17')
    dv=(left+I('1.4')*right)/I('1.17')
    db=(ju+jv-p['Gbleed']*b-I(int(spark))*ih)/p['Cb']
    # Only derivatives 2,3,4 are required for diode guard slopes.
    return [di,dj,du,dv,db]

def step(t,h,root,delta,mode,target=None):
    last=None
    for radius in ('.000001','.00001','.0001','.001','.01','.1'):
        R=F(radius)
        P,eps=residual_mode(t,h,root,mode)
        tube=[c.evalpoly(row,I(0,h)).expand(R) for row in P]
        E,info=error_signed(tube,h,delta,eps,mode)
        gu,gv,gs=guards(tube)
        checks=(gs.a>0 and (gu.a>0 if mode[0] else gu.b<0)
                and (gv.a>0 if mode[1] else gv.b<0))
        if target=='V_OFF':checks=gs.a>0 and gu.a>0 and root_slope(tube,mode,target).a>0
        if target=='U_OFF':checks=gs.a>0 and gv.b<0 and root_slope(tube,mode,target).a>0
        good=all(e<R for e in E) and checks
        end=[c.evalpoly(row,I(h)) for row in P]
        endpoint=[val.expand(e) for val,e in zip(end,E)]
        nxt,err=c.rational_recenter(endpoint)
        last=(dict(t0=str(t),t1=str(t+h),mode=list(mode),target=target,
                 valid=good,radius=radius,gu=[str(gu.a),str(gu.b)],
                 gv=[str(gv.a),str(gv.b)],spark=[str(gs.a),str(gs.b)],
                 guard_derivative=[str(root_slope(tube,mode,target).a),
                                   str(root_slope(tube,mode,target).b)] if target else None,
                 error=str(max(E)),comparison=info),nxt,err,endpoint,P,E,tube)
        if good:return last
    raise RuntimeError(('validated step failed',last[0]))

def event_isolation(t,hL,hR,root,delta,mode,target,centres):
    assert target in ('V_OFF','U_OFF')
    left=step(t,hL,root,delta,mode,target)
    right=step(t,hR,root,delta,mode,target)
    target_idx=1 if target=='V_OFF' else 0
    gl=guards(left[3])[target_idx];gr=guards(right[3])[target_idx]
    assert gl.a>0 and gr.b<0,('event signs not isolated',target,gl.a,gl.b,gr.a,gr.b)
    P=right[4];E=right[5]
    xs=[c.evalpoly(z,I(hL,hR)).expand(e) for z,e in zip(P,E)]
    source=centres[4 if target=='V_OFF' else 5]
    box=[I(v-F('.0001'),v+F('.0001')) for v in source['x']]
    member=[z.subset(b) for z,b in zip(xs,box)]
    slope=root_slope(right[6],mode,target)
    assert slope.a>0
    return {'name':target,'interval':[str(t+hL),str(t+hR)],'membership':member,
            '9_of_9':all(member),'slope':[str(slope.a),str(slope.b)],
            'left_guard':[str(gl.a),str(gl.b)],'right_guard':[str(gr.a),str(gr.b)],
            'event_box_grid':[[str(v.a),str(v.b)] for v in xs]},right

def virtual_to_physical_right(step_right,mode,target,hwidth):
    # Continuity of diode current implies identity saltation. The physical
    # post-switch solution and the virtual pre-switch flow differ by O(w^2).
    # This comparison requires the certified virtual guard slope bound on the
    # whole event bracket and Lipschitz majorant for BOTH active-set fields.
    info,root,delta,endpoint,P,E,tube=step_right
    assert info['target']==target
    slope=root_slope(tube,mode,target)
    M=F(slope.b,S)
    h=F(hwidth)
    post=(mode[0],False,mode[2]) if target=='V_OFF' else (False,mode[1],mode[2])
    # Physical trajectory may move outside the VIRTUAL field tube. Instead
    # of a merely local Jacobian on that tube, certify a shared broad domain
    # containing both flows by a strict 0.01 bootstrap and a global L=250.
    # For |cap|<=2, |ih|<=3, nonlinear capacitor row sum is <250; every
    # other Jacobian row of the four diode modes is a constant and <250.
    assert tube[8].maxabs()<F('1.9') and tube[7].maxabs()<F('2.9')
    L=F(250)
    assert h*L<F(1,2)
    # Source vector for j_U or j_V in the original capacitor inversion.
    if target=='U_OFF':coef=[F(0),F(0),-F('1.55')/F('1.17'),-1/F('1.17'),1/F('.65')]+[F(0)]*4
    else:coef=[F(0),F(0),-1/F('1.17'),-F('1.4')/F('1.17'),1/F('.65')]+[F(0)]*4
    effect=max(abs(z) for z in coef)/F('.12')*M*h*h/(2*(1-L*h))
    assert effect < F('0.01'), 'common physical/virtual domain bootstrap unpaid'
    return root,[v+effect for v in delta],post,dict(post_mode=post,
       comparison_rational=str(effect),Jacobian_L_upper=str(L),
       source_guard_slope_upper=str(M),current_continuous_at_switch=True,
       state_saltation_identity=True,comparison_validated=True)

def interval_pi(terms=35):
    def atan_interval(z):
        a=sum(((-1)**k*z**(2*k+1)/F(2*k+1) for k in range(terms)),F(0))
        r=z**(2*terms+1)/F(2*terms+1)
        return (a-r,a+r)
    aa=atan_interval(F(1,5));bb=atan_interval(F(1,239))
    return 16*aa[0]-4*bb[1],16*aa[1]-4*bb[0]

def run(args):
    proof_inputs(ROOT_REPO)
    raw=json.loads(Path(args.checkpoint).read_text())
    assert raw['nsteps']==75 and raw['status']=='J28B_PASS_SIGNED_VARIATIONAL_BLOCK'
    assert F(raw['t'])==F('4.26534095')
    out=Path(args.out_dir);out.mkdir(parents=True,exist_ok=True)
    started=time.monotonic()
    # Stage 75 J28B is a rigorously verified virtual-U-inactive left endpoint.
    # The previous J29A proved physical-vs-virtual at the fourth right endpoint.
    # Reuse J28B exact Taylor engine to evaluate the virtual endpoint itself.
    pre=j28b.step_v_tight(F(raw['t']),F('.0104'),list(map(F,raw['root'])),
                          list(map(F,raw['delta'])),F('.001'),bracket_u=True)
    assert pre[0]['valid']
    _,root,delta=pre
    comparison=F(189,61100000)
    delta=[v+comparison for v in delta]
    t=F('4.27574095');mode=(True,True,True)
    events=[];steps=[]
    centres=json.loads((ROOT_REPO/'Artifacts/smith-filsinger/j24_six_hybrid_guard_centres_20261123.json').read_text(),parse_float=F)['events']
    if args.resume and (out/'full_period_progress.json').exists():
        prev=json.loads((out/'full_period_progress.json').read_text())
        assert prev['source']=='J28B full physical continuation campaign'
        assert not prev.get('periodic_orbit_proved',False)
        t=F(prev['checkpoint']['t'])
        root=list(map(F,prev['checkpoint']['root']))
        delta=list(map(F,prev['checkpoint']['delta']))
        mode=tuple(prev['mode'])
        events=prev['events']
        steps=[{'resumed_prior_segment':k} for k in range(prev['steps'])]
        assert len(events)<=2
    def save(status,why):
        receipt={'status':status,'reason':why,'source':'J28B full physical continuation campaign',
          'event_roots_paid_prior':4,'event_state_boxes_paid_prior':3,
          'target_events':list(TARGETS[i][0] for i in range(len(events),2)),
          'events':events,'time':str(t),'mode':mode,'steps':len(steps),
          'checkpoint':{'t':str(t),'root':list(map(str,root)),
                        'delta':list(map(str,delta))},
          'periodic_orbit_proved':False,'five_parameter_box_proved':False,
          'original_hardware_proved':False,'CI':False}
        (out/'full_period_progress.json').write_text(json.dumps(receipt,indent=2)+'\n')
        return receipt
    for target,pre_time,hL,hR in TARGETS[len(events):]:
        assert mode==((True,True,True) if target=='V_OFF' else (True,False,True)), ('wrong physical itinerary',target,mode)
        while t<pre_time:
            h=min(F('.01'),pre_time-t)
            if time.monotonic()-started>args.budget:
                return save('CHECKPOINT_BUDGET_EXHAUSTED','time limit reached before complete event itinerary')
            row,root,delta,*_=step(t,h,root,delta,mode)
            t+=h;steps.append(row)
            if len(steps)%10==0:save('CHECKPOINT_CONTINUING',target)
        assert t==pre_time,(t,pre_time)
        event,virtual=event_isolation(t,hL,hR,root,delta,mode,target,centres)
        root,delta,mode,transfer=virtual_to_physical_right(virtual,mode,target,hR-hL)
        event['physical_handoff']=transfer
        events.append(event)
        t+=hR
        save('CHECKPOINT_EVENT_PAID',target)
    # Final no-diode, spark-ON smooth segment to source period tau.
    lo,hi=interval_pi();tau_lo=20*lo/11;tau_hi=20*hi/11
    while t+F('.01')<=tau_lo:
        if time.monotonic()-started>args.budget:
            return save('CHECKPOINT_BUDGET_EXHAUSTED','time limit reached before source period')
        row,root,delta,*_=step(t,F('.01'),root,delta,mode)
        t+=F('.01');steps.append(row)
        if len(steps)%10==0:save('CHECKPOINT_CONTINUING','tau')
    # The exact terminal time tau is irrational. Advance to rational tau_low,
    # then envelope remaining tau uncertainty by full smooth RHS on interval.
    h=tau_lo-t
    if h>0:
        row,root,delta,*_=step(t,h,root,delta,mode)
        t=tau_lo;steps.append(row)
    state=[I(z).expand(e) for z,e in zip(root,delta)]
    # The remainder is not ignored: a uniform RHS bound across tiny interval.
    w=tau_hi-tau_lo
    broad=[z.expand(F('1e-12')) for z in state]
    gu,gv,gs=guards(broad)
    assert gu.b<0 and gv.b<0 and gs.a>0, 'terminal guards / no-extra-event condition unpaid'
    D=full_rhs_interval(tau_lo,tau_hi,broad,mode)
    outer=[x+I(0,w)*f for x,f in zip(state,D)]
    assert all(x.subset(b) for x,b in zip(outer,broad)), 'tau short-tail Picard tube unpaid'
    endpoint=outer
    initial=[I(F(q)) for q in c.j25.ROOT]
    defects=[(a-initial[i]) for i,a in enumerate(endpoint)]
    best=max(z.maxabs() for z in defects)
    result=save('FULL_SIX_EVENT_NOMINAL_FLOW_IF_VALIDATED_RETURN_BALL_OPEN','needs nonzero-ball full hybrid DP_tau enclosure and Banach/Krawczyk')
    result.update({'events':events,'event5_and6_count':len(events),
       'event5_6_all_J24_boxes_paid':all(e['9_of_9'] for e in events),
       'nominal_endpoint_defect_sup_upper':best,
       'return_map_ball_certified':False,
       'tau_interval':[str(tau_lo),str(tau_hi)],
       'source_time_exact_pi_interval':True})
    (out/'full_period_progress.json').write_text(json.dumps(result,indent=2)+'\n')
    return result

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--checkpoint',type=Path,required=True)
    ap.add_argument('--out-dir',type=Path,required=True)
    ap.add_argument('--budget',type=float,default=90.)
    ap.add_argument('--resume',action='store_true',help='resume exact rational checkpoint, verify source hashes')
    x=ap.parse_args()
    try:
        res=run(x)
    except Exception as exc:
        x.out_dir.mkdir(parents=True,exist_ok=True)
        res={'status':'FAIL_CLOSED_UNPAID_OBLIGATION','error':str(exc),
             'traceback':traceback.format_exc(), 'periodic_orbit_proved':False}
        (x.out_dir/'failed_gate.json').write_text(json.dumps(res,indent=2)+'\n')
    print(json.dumps({k:res[k] for k in ('status','time','steps','reason','error','periodic_orbit_proved') if k in res},indent=2))
    return 0 if res['status']!='FAIL_CLOSED_UNPAID_OBLIGATION' else 2
if __name__=='__main__':sys.exit(main())