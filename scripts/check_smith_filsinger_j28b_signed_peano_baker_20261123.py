"""J28B: validated signed Peano-Baker and fourth diode-U event (nominal).

All operations use J25 exact integer-grid outward rounding. J(t) is enclosed
by common interval matrix on the entire smooth tube; Peano-Baker terms in
[J]^n h^n/n! enclose noncommuting time-ordered products, geometric norm tail.
"""
from fractions import Fraction as F
import math, json, argparse
from pathlib import Path
import check_smith_filsinger_j27_second_spark_off_validated_20261123 as j27
import check_smith_filsinger_j28_spark_return_on_interval_20261123 as j28
c=j27.c; I,S,p = c.I,c.S,c.p

def jsigned(tube):
 cap=tube[8];ih=tube[7]
 Z=I(0);J=[[Z for _ in range(9)] for _ in range(9)]
 J[0][0]=-p['R1']*I('1.5')/I('2.64')
 J[0][1]=p['M']*p['R2']/I('2.64');J[0][2]=-p['M']/I('2.64');J[0][3]=p['M']/I('2.64')
 J[1][0]=p['M']*p['R1']/I('2.64');J[1][1]=-p['L1']*p['R2']/I('2.64');J[1][2]=p['L1']/I('2.64');J[1][3]=-p['L1']/I('2.64')
 J[2][1]=-I('.55')/I('1.17');J[2][5]=I('1.55')*p['k']/I('1.17');J[2][7]=I('1.55')*p['kh']/I('1.17')
 J[3][1]=I('.4')/I('1.17');J[3][5]=p['k']/I('1.17');J[3][7]=p['kh']/I('1.17')
 J[4][4]=-p['Gbleed']/p['Cb'];J[4][7]=-I(1)/p['Cb']
 J[5][2]=-p['k']/I(2);J[5][5]=-p['gamma_rad']-p['gamma_internal'];J[5][6]=p['omega']
 J[6][5]=-p['omega'];J[6][6]=-p['gamma_rad']-p['gamma_internal']
 J[7][2]=-p['kh']/p['Lh'];J[7][4]=I(1)/p['Lh'];J[7][7]=-(p['Rcoil']+p['Rgap'])/p['Lh'];J[7][8]=-I(1)/p['Lh']
 den=I(1)+I('1.5')*cap**2
 J[8][7]=I(1)/(p['Ch']*den)
 J[8][8]=-p['Gload']/(p['Ch']*den)-(ih-p['Gload']*cap)*I(3)*cap/(p['Ch']*den**2)
 g=I(1)/p['Rd'];
 J[2][3]=-g/I('1.17');J[2][4]=g/I('1.17')
 J[3][3]=-I('1.4')*g/I('1.17');J[3][4]=I('1.4')*g/I('1.17')
 J[4][3]=g/p['Cb'];J[4][4]=-(p['Gbleed']+g)/p['Cb']
 return J

def mmul(A,B):
 D=len(A); C=len(B[0]); shared=len(B)
 return [[sum((A[i][k]*B[k][j] for k in range(shared)),I(0)) for j in range(C)] for i in range(D)]

def exp_bound_signed(J,h,N=8):
 h=F(h); D=len(J)
 eye=[[I(int(i==j)) for j in range(D)] for i in range(D)]
 term=eye
 result=[[v for v in row] for row in eye]
 for n in range(1,N+1):
  product=mmul(term,J)
  term=[[v*I(h/F(n)) for v in row] for row in product]
  result=[[a+b for a,b in zip(x,y)] for x,y in zip(result,term)]
 L=max(sum(F(max(abs(x.a),abs(x.b)),S) for x in row) for row in J)
 lam=h*L
 assert lam < N+2,(lam,N)
 tail=(lam**(N+1)/math.factorial(N+1))/(1-lam/F(N+2))
 T=I(0,tail)
 return [[val.expand(tail) for val in row] for row in result],L,tail

def componentwise_endpoint_error(X,h,delta,eps):
 J=jsigned(X)
 Phi,L,tail=exp_bound_signed(J,h)
 init=[sum((F(max(abs(x.a),abs(x.b)),S)*d for x,d in zip(row,delta)),F(0)) for row in Phi]
 forcing=c.bound_exp(j27.get_A_v(X),h,[F(0)]*9,eps)
 return [a+b for a,b in zip(init,forcing)],dict(jacobian_L=float(L),peano_tail=float(tail),error_contribution_init_max=float(max(init)),error_contribution_forcing_max=float(max(forcing)))

def diode_U_slope(X):
    i,j,u,v,b,q,r,ih,cap=X
    vcurrent=(v-b-p['Vd'])/p['Rd']
    left=-j+p['k']*q+p['kh']*ih
    right=j-vcurrent
    du=(I('1.55')*left+right)/I('1.17')
    db=(vcurrent-p['Gbleed']*b-ih)/p['Cb']
    return du-db

def step_v_tight(t,h,root,delta,R,N=52,bracket_u=False):
 t=F(t);h=F(h);R=F(R)
 P,eps=j27.residual_v(N,t,root,h)
 X=[c.evalpoly(row,I(0,h)).expand(R) for row in P]
 gu,gv,gs=c.guards(X)
 E,info=componentwise_endpoint_error(X,h,delta,eps)
 gu_slope=diode_U_slope(X)
 valid=all(e<R for e in E) and gv.a>0 and gs.a>0
 if bracket_u:valid=valid and gu_slope.a>0
 else:valid=valid and gu.b<0
 end=[c.evalpoly(row,I(h)) for row in P]
 endbox=[z.expand(e) for z,e in zip(end,E)]
 gu_end=endbox[2]-endbox[4]-p['Vd']
 root_n,delta_n=c.rational_recenter(endbox)
 return dict(valid=valid,t0=str(t),t1=str(t+h),radius=str(R),error_max=float(max(E)),
             guardUupper=gu.b/S,guardUend_numerators=[str(gu_end.a),str(gu_end.b)],
             guardU_slope_numerators=[str(gu_slope.a),str(gu_slope.b)],
             guardVlower=gv.a/S,spark_lower=gs.a/S,**info),root_n,delta_n

def initial_handoff():
    # Executing J28 also replays J27 and all first three exact event gates.
    receipt=j28.run()
    assert receipt['third_J24_spark_ON_box_included_all_nine']
    tL=F('3.51534025');tR=F('3.51534095');dt=tR-tL
    z0=[I(int(a),int(b),raw=True) for a,b in receipt['third_event_state_grid']]
    tube=[z.expand(F('.0001')) for z in z0]
    rhs_off=j28.interval_rhs_off(tL,tR,tube)
    rhs_on=rhs_off[:]
    rhs_on[4]=rhs_on[4]-tube[7]/p['Cb']
    rhs_on[7]=rhs_on[7]+(tube[4]-p['Rgap']*tube[7])/p['Lh']
    assert all((z+I(0,dt)*f).subset(T) for z,f,T in zip(z0,rhs_on,tube))
    assert all((z+I(0,dt)*f).subset(T) for z,f,T in zip(z0,rhs_off,tube))
    assert (tube[2]-tube[4]-p['Vd']).b<0
    assert (tube[3]-tube[4]-p['Vd']).a>0
    assert (tube[4]-p['Voff']).a>0
    A=j27.get_A_v(tube);L=max(map(sum,A))
    assert L*dt<F(1,2)
    src=[F(0)]*9
    src[4]=F(c.supabs(tube[7]/p['Cb']),S)
    src[7]=F(c.supabs((tube[4]-p['Rgap']*tube[7])/p['Lh']),S)
    err=c.bound_exp(A,dt,[F(0)]*9,src)
    virtual=[I(F(v)).expand(F(d)) for v,d in zip(receipt['virtual_OFF_right_root'],receipt['virtual_OFF_right_delta'])]
    physical=[z.expand(e) for z,e in zip(virtual,err)]
    root,delta=c.rational_recenter(physical)
    return dict(status='J28B_PASS_CORRELATED_SPARK_ON_HANDOFF',t=str(tR),
       nsteps=0,root=[str(v) for v in root],delta=[str(v) for v in delta],
       source_J28_three_event_pass=True,source_J24_boxes_paid=3,
       jump_sources=[str(q) for q in src],
       comparison_error_upper_grid=[str(c.j25.ceil_div(v.numerator*S,v.denominator)) for v in err],
       comparison_error_max_approx=float(max(err)),
       original_time_uncertainty=str(dt),
       reference_virtual_OFF_at_same_fixed_time=True,
       no_event_state_time_independence_assumed=True,
       Picard_both_spark_modes=True,Picard_ON_L_upper=str(L),
       noninterval_ambient_source_measured=False,periodic_orbit_proved=False)

def advance(input_receipt,count=20):
    x=input_receipt
    assert x['status'] in ('J28B_PASS_CORRELATED_SPARK_ON_HANDOFF','J28B_PASS_SIGNED_VARIATIONAL_BLOCK')
    t=F(x['t']);root=list(map(F,x['root']));delta=list(map(F,x['delta']))
    n0=x['nsteps'];assert n0<75
    count=min(count,75-n0)
    rows=[]
    for i in range(count):
        found=None
        for r in ('.000001','.00001','.0001','.001'):
            row,nxt,dn=step_v_tight(t,F('.01'),root,delta,F(r))
            if row['valid']:
                found=row,nxt,dn;break
        assert found is not None,(str(t),row)
        row,root,delta=found;t+=F('.01');rows.append(row)
    return dict(status='J28B_PASS_SIGNED_VARIATIONAL_BLOCK',
       t=str(t),nsteps=n0+count,root=[str(v) for v in root],
       delta=[str(v) for v in delta],segments=rows,
       max_component_error_approx=rows[-1]['error_max'],
       last_U_guard_upper=rows[-1]['guardUupper'],
       all_segments_checked_with_signed_Peano_Baker=True,
       interval_Nonlinear_Jacobian_and_exact_52_order_defect=True,
       no_extra_diodes_or_sparks=True,periodic_orbit_proved=False)

def isolate_fourth(x):
    assert x['status']=='J28B_PASS_SIGNED_VARIATIONAL_BLOCK'
    assert x['nsteps']==75 and F(x['t'])==F('4.26534095')
    t=F(x['t']);root=list(map(F,x['root']));delta=list(map(F,x['delta']))
    hL=F('.0098');hR=F('.0104')
    a,_,_=step_v_tight(t,hL,root,delta,F('.001'),bracket_u=True)
    b,_,_=step_v_tight(t,hR,root,delta,F('.001'),bracket_u=True)
    assert a['valid'] and b['valid']
    assert int(a['guardUend_numerators'][1])<0
    assert int(b['guardUend_numerators'][0])>0
    assert int(b['guardU_slope_numerators'][0])>0
    P,eps=j27.residual_v(52,t,root,hR)
    tube=[c.evalpoly(row,I(0,hR)).expand(F('.001')) for row in P]
    E,_=componentwise_endpoint_error(tube,hR,delta,eps)
    event_state=[c.evalpoly(row,I(hL,hR)).expand(e) for row,e in zip(P,E)]
    source=json.loads((Path(__file__).resolve().parents[1]/'Artifacts/smith-filsinger/j24_six_hybrid_guard_centres_20261123.json').read_text(),parse_float=F,parse_int=F)['events']
    assert source[3]['kind']=='diode' and source[3]['name']=='U'
    member=[q.subset(I(z-F('.0001'),z+F('.0001'))) for q,z in zip(event_state,source[3]['x'])]
    # The event exists but the original J24 radius-1e-4 box is NOT paid.
    assert not all(member) # exact full original J24 event-state box remains unpaid
    return dict(status='J28B_PASS_FOURTH_GUARD_ROOT_BUT_J24_BOX_PENDING',
       U_activation_time_bracket=[str(t+hL),str(t+hR)],
       first_three_J24_boxes_included=True,
       fourth_event_root_exists_and_unique=True,
       guard_U_left_endpoint=a['guardUend_numerators'],
       guard_U_right_endpoint=b['guardUend_numerators'],
       guard_U_positive_derivative=b['guardU_slope_numerators'],
       other_diodes_and_spark_guard_excluded=True,
       event_state_grid=[[str(q.a),str(q.b)] for q in event_state],
       J24_fourth_original_box_coordinate_membership=member,
       J24_fourth_coordinate_membership_count=sum(member),
       J24_fourth_original_box_all_nine_included=False,
       validated_crossings=4,original_J24_event_boxes_paid=3,
       original_J24_event_boxes_total=6,
       physical_after_U_activation_not_integrated=True,
       exact_periodic_orbit_proved=False,
       uniform_five_parameter_family_proved=False,
       physical_environmental_power_measured=False,ci_used=False)

def run_cli():
    ap=argparse.ArgumentParser()
    ap.add_argument('--mode',choices=('handoff','advance','event'),required=True)
    ap.add_argument('--input',type=Path)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--count',type=int,default=20)
    a=ap.parse_args()
    assert a.mode=='handoff' or (a.input is not None and a.input.exists())
    data=(initial_handoff() if a.mode=='handoff' else
          advance(json.loads(a.input.read_text()),a.count) if a.mode=='advance'
          else isolate_fourth(json.loads(a.input.read_text())))
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:data[k] for k in data if k in ('status','t','nsteps','U_activation_time_bracket','validated_crossings','original_J24_event_boxes_paid')},sort_keys=True))

if __name__=='__main__':run_cli()
