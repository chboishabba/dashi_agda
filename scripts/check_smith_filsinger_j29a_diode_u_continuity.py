#!/usr/bin/env python3
"""J29A: source-owned exact rational local diode-U handoff obligations.

Runs without CI, floats or a numerical ODE solver. Consumes the J28B certified
75-step rational checkpoint and its already validated fourth-event guard bracket.
This proves a local physical switched-ODE Picard tube, strictly positive
U crossing slope, and a quadratic handoff comparison bound. It does NOT
prove J24 fourth event-box inclusion or the full-period return map.
"""
from fractions import Fraction as F
from pathlib import Path
import json
from itertools import product
from hashlib import sha256

q=lambda s: F(str(s))
class I:
    def __init__(self,a,b=None):
        self.a=F(a); self.b=self.a if b is None else F(b)
        assert self.a<=self.b
    def __add__(self,v):
        v=iv(v);return I(self.a+v.a,self.b+v.b)
    __radd__=__add__
    def __neg__(self):return I(-self.b,-self.a)
    def __sub__(self,v):return self+-iv(v)
    def __rsub__(self,v):return iv(v)+-self
    def __mul__(self,v):
        v=iv(v); z=[self.a*v.a,self.a*v.b,self.b*v.a,self.b*v.b]
        return I(min(z),max(z))
    __rmul__=__mul__
    def __truediv__(self,v):
        v=iv(v); assert v.a>0 or v.b<0
        return self*I(1/v.b,1/v.a)
    def sq(self):
        if self.a>=0:return I(self.a*self.a,self.b*self.b)
        if self.b<=0:return I(self.b*self.b,self.a*self.a)
        return I(0,max(self.a*self.a,self.b*self.b))
    def positive(self):return I(max(0,self.a),max(0,self.b))
    def subset(self,v):return self.a>=v.a and self.b<=v.b
    def encloses(self,low,high):return self.a<=low and self.b>=high
    def maxabs(self):return max(abs(self.a),abs(self.b))
    def decimals(self):return [float(self.a),float(self.b)]
def iv(v):return v if isinstance(v,I) else I(v)
p={k:q(v) for k,v in dict(L1='2',L2='1.5',M='.6',R1='.35',R2='.28',C='1',Cu='.4',Cv='.55',Cb='.65',Rd='.12',Vd='.1',Gbleed='.018',Von='.006',Voff='.0018',omega='1.1',gamma_rad='.015',gamma_internal='.0002',k='.35',source_amp='1.2',Lh='.15',Ch='.12',alpha='.5',Rgap='.09',Rcoil='.05',Gload='.52',kh='2').items()}
# sqrt(0.03) in [0.17,0.18], certified by squaring rationals.
RAD=I(F(17,100),F(18,100))
assert RAD.a**2<F(3,100)<RAD.b**2

def physical_field(X):
    """Set-valued enclosure for both diode switches, spark physically ON.

    Incoming sin and cos are each in [-1,1] at all times. No fake sampled
    source phase is used. This is intentionally a broad Picard containment.
    """
    i,j,u,v,b,q0,r,ih,x=X
    ju=((u-b-p['Vd'])/p['Rd']).positive()
    jv=((v-b-p['Vd'])/p['Rd']).positive()
    a=-p['R1']*i; bb=u-v-p['R2']*j
    di=(p['L2']*a-p['M']*bb)/F('2.64')
    dj=(-p['M']*a+p['L1']*bb)/F('2.64')
    left=-j-ju+p['k']*q0+p['kh']*ih
    right=j-jv
    du=(F('1.55')*left+right)/F('1.17')
    dv=(left+F('1.4')*right)/F('1.17')
    db=(ju+jv-p['Gbleed']*b-ih)/p['Cb']
    gamma=p['gamma_rad']+p['gamma_internal']
    dq=p['omega']*r-gamma*q0-p['k']*u/2+RAD*p['source_amp']*I(-1,1)
    dr=-p['omega']*q0-gamma*r+RAD*p['source_amp']*I(-1,1)
    dih=(b-x-(p['Rcoil']+p['Rgap'])*ih-p['kh']*u)/p['Lh']
    dx=(ih-p['Gload']*x)/(p['Ch']*(I(1)+F('1.5')*x.sq()))
    return [di,dj,du,dv,db,dq,dr,dih,dx]

def jacobian_first_eight(U,V):
    J=[[F(0) for _ in range(9)] for _ in range(8)]
    def add(i,k,val):J[i][k]+=F(val)
    A=F('2.64');B=F('1.17');d=p['Rd']
    add(0,0,-p['L2']*p['R1']/A);add(0,1,p['M']*p['R2']/A);add(0,2,-p['M']/A);add(0,3,p['M']/A)
    add(1,0,p['M']*p['R1']/A);add(1,1,-p['L1']*p['R2']/A);add(1,2,p['L1']/A);add(1,3,-p['L1']/A)
    add(2,1,-F('.55')/B);add(2,5,F('1.55')*p['k']/B);add(2,7,F('1.55')*p['kh']/B)
    add(3,1,F('.4')/B);add(3,5,p['k']/B);add(3,7,p['kh']/B)
    if U:
        add(2,2,-F('1.55')/(B*d));add(2,4,F('1.55')/(B*d))
        add(3,2,-1/(B*d));add(3,4,1/(B*d))
        add(4,2,1/(p['Cb']*d));add(4,4,-1/(p['Cb']*d))
    if V:
        add(2,3,-1/(B*d));add(2,4,1/(B*d))
        add(3,3,-F('1.4')/(B*d));add(3,4,F('1.4')/(B*d))
        add(4,3,1/(p['Cb']*d));add(4,4,-1/(p['Cb']*d))
    add(4,4,-p['Gbleed']/p['Cb']);add(4,7,-1/p['Cb'])
    add(5,2,-p['k']/2);add(5,5,-p['gamma_rad']-p['gamma_internal']);add(5,6,p['omega'])
    add(6,5,-p['omega']);add(6,6,-p['gamma_rad']-p['gamma_internal'])
    add(7,2,-p['kh']/p['Lh']);add(7,4,1/p['Lh']);add(7,7,-(p['Rcoil']+p['Rgap'])/p['Lh']);add(7,8,-1/p['Lh'])
    return J

def run(checkpoint_path):
    raw=Path(checkpoint_path).read_bytes(); ck=json.loads(raw)
    assert ck['status']=='J28B_PASS_SIGNED_VARIATIONAL_BLOCK' and ck['nsteps']==75
    assert F(ck['t'])==F('4.26534095')
    root=list(map(F,ck['root'])); delta=list(map(F,ck['delta']))
    x0=[I(v-d,v+d) for v,d in zip(root,delta)]
    assert len(x0)==9 and max(delta)<F('0.0003')
    h=F('0.0104')
    radius=F('.2')
    B=[I(x-radius,x+radius) for x in root]
    D=physical_field(B)
    C=[x+I(0,h)*d for x,d in zip(x0,D)]
    slacks=[min(c.a-x.a,x.b-c.b) for c,x in zip(C,B)]
    assert all(s>0 for s in slacks), ('broad Picard self-inclusion failed',list(map(float,slacks)))
    # Monotone Picard refinement: if C=X0+[0,h] f(B) subset B, then C is
    # itself self-inclusive because f(C) subset f(B). Preserve exact rationals.
    refinements=0
    for k in range(12):
        D=physical_field(B)
        C=[x+I(0,h)*d for x,d in zip(x0,D)]
        assert all(c.subset(b) for c,b in zip(C,B))
        B=C;refinements+=1
    # This is one enclosure for the ACTUAL full positive-part diode hybrid
    # physical flow, including the U diode root, not virtual U-off extension.
    gv=B[3]-B[4]-p['Vd']
    gs=B[4]-p['Voff']
    dgU=physical_field(B)[2]-physical_field(B)[4]
    assert gv.a>0 and gs.a>0 and dgU.a>0
    assert (B[4]-p['Voff']).a>0
    assert B[7].a>-2 and B[7].b<2 and B[8].a>-1 and B[8].b<1
    row_norms=[sum(map(abs,row)) for U,V in product((0,1),repeat=2) for row in jacobian_first_eight(U,V)]
    # Nonlinear capacitor row, exact analytical bound for |x|<=1, |ih|<=2,
    # denominator g=1+1.5*x²>=1; 
    # |d_x f_x| <= Gload/Ch + 3*(2+Gload)/(Ch),
    # |d_ih f_x| <= 1/Ch.
    cap_row=p['Gload']/p['Ch']+3*(2+p['Gload'])/p['Ch']+1/p['Ch']
    L=max(row_norms+[cap_row])
    assert L<100,('global Lipschitz bound failed',float(L))
    # The diode U vector field jump vanishes exactly on the guard gU=0:
    # f_{Uon}-f_{Uoff}= (gU/Rd) * (0,0,-1.55/1.17,-1/1.17,1/Cb,0,0,0,0).
    coeff=[F(0),F(0),-F('1.55')/F('1.17'),-1/F('1.17'),1/p['Cb'],F(0),F(0),F(0),F(0)]
    n=[0,0,1,0,-1,0,0,0,0]
    Umat=jacobian_first_eight(1,1); Omat=jacobian_first_eight(0,1)
    for i in range(8):
        for j in range(9):assert Umat[i][j]-Omat[i][j]==coeff[i]*n[j]/p['Rd']
    assert coeff[8]==0 and sum(int(z!=0) for z in coeff)==3
    # Both mode RHSs agree at the actual guard (diode current=0), so saltation
    # is identity: I+(f_on-f_off)*nᵀ/(nᵀ f_off) = I.
    # The inherited J28B fourth-root upper slope is 1.25043921553...
    M=F(126,100); w=F(6,10000)
    raw_derivative_upper=F('1.250439215531312157277744411153')
    assert raw_derivative_upper<M
    assert w*100<1
    # For the physical state vs U-inactive virtual state at fixed tR, use
    # Gronwall on the continuous positive-part diode field with Lipschitz <=100.
    # gU_virtual(t*)=0; gU_virtual <= M(t-t*). Forcing is quadratic in w.
    A=max(map(abs,coeff))/p['Rd']
    bound=A*M*w*w/(2*(1-100*w)) # exp(Lw) <= 1/(1-Lw)
    assert bound==F(189,61100000) and bound<F(1,300000)
    return {
      'status':'J29A_PASS_EXACT_LOCAL_U_SWITCH_CONTINUITY_AND_QUADRATIC_HANDOFF_BOUND',
      'checkpoint_selected_values_sha256':sha256(json.dumps({key:ck[key] for key in ('status','t','nsteps','root','delta')}, sort_keys=True,separators=(',',':')).encode()).hexdigest(),
      'checkpoint_original_Git_blob_expected':'74c1a94b30c44a772016c93b39558bc446359832',
      'original_checkpoint_raw_bytes_replayed':False,
      'checkpoint_headtime':str(F(ck['t'])),
      'certified_root_bracket_inherited':['4.27514095','4.27574095'],
      'model_time_duration_0p0104_Picard_tube':{'start':'4.26534095','end':'4.27574095','radius':str(radius),'exact_positive_Picard_slack_min':str(min(slacks)), 'all_9_coordinate_initial_error_included':True},
      'global_piecewise_Lipschitz_bound_analytic':str(L),
      'monotone_Picard_refinement_rounds':refinements,
      'refined_tube_coordinate_approx':[z.decimals() for z in B],
      'actual_U_guard_derivative_lower_approx':float(dgU.a),
      'actual_V_guard_lower_approx':float(gv.a),
      'fully_physical_diode_U_activation_through_common_right_endpoint':True,
      'actual_V_guard_lower':str(gv.a),'actual_spark_guard_lower':str(gs.a),
      'actual_U_guard_derivative_lower':str(dgU.a),
      'actual_U_guard_derivative_upper':str(dgU.b),
      'physical_trajectory_no_other_switch_in_window':True,
      'proof_L_upper':'100',
      'U_on_minus_U_off_nonzero_indices':[2,3,4],
      'no_state_reset':True,'field_continuous_at_U_guard':True,
      'diode_U_saltation_identity':True,
      'Jacobian_jump_rank_one':True,
      'Gronwall_comparison_uses_inherited_J28B_positive_guard_slope_upper':str(raw_derivative_upper),
      'guard_slope_coarse_upper_used':str(M),'event_width':str(w),
      'post_U_activation_common_endpoint_difference_upper_exact':str(bound),
      'post_U_activation_common_endpoint_difference_upper_decimal':float(bound),
      'fourth_J24_original_box_admitted':False,'actual_U_active_flow_integrated':True,
      'five_parameter_family_proved':False,'periodic_orbit_proved':False,
      'source_apparatus_measured':False,'CI':False,'Agda':False}

if __name__=='__main__':
    path=Path(__file__).resolve().parents[1]/'Artifacts/smith-filsinger/j28b_signed_75_step_exact_checkpoint_20261123.json'
    print(json.dumps(run(path),indent=2,sort_keys=True))
