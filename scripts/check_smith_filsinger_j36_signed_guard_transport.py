"""J36 conditional original J31/J35 source-graph interval consumer.

Input chart derivatives, event tubes, guard signs, and centre return must
come from admitted original-source producers. This file does not certify
those inputs or the original periodic orbit. --self-test checks exact algebra.
"""
import argparse,json
from fractions import Fraction as F
from pathlib import Path


def self_test():
    import sympy as S
    q=S.Rational; u,v,b,ih=S.symbols('u v b ih',real=True)
    modes=((0,0,1),(0,1,1),(0,1,0),(0,1,1),(1,1,1),(1,0,1),(0,0,1))
    def switched(m):
        U,V,c=m; ju=U*(u-b-q(1,10))/q(3,25); jv=V*(v-b-q(1,10))/q(3,25)
        z=S.zeros(9,1); z[2]=(-q(155,100)*ju-jv)/q(117,100)
        z[3]=(-ju-q(14,10)*jv)/q(117,100);z[4]=(ju+jv-c*ih)/q(65,100)
        z[7]=c*(b-q(9,100)*ih)/q(15,100);return z
    for k in range(6):
        sub={v:b+q(1,10)} if k in (0,4) else {u:b+q(1,10)} if k in (3,5) else {b:q(18,10000) if k==1 else q(6,1000)}
        d=(switched(modes[k+1])-switched(modes[k])).subs(sub).applyfunc(S.simplify)
        if k in (0,3,4,5):assert d==S.zeros(9,1)
        else:
            dc=modes[k+1][2]-modes[k][2]; expected=S.zeros(9,1)
            expected[4]=-dc*ih/q(65,100);expected[7]=dc*(sub[b]-q(9,100)*ih)/q(15,100)
            assert d==expected
    # For an arbitrary transverse event, moving-event sensitivity and
    # fixed-clock saltation transport agree, including the signed jump.
    fm,fp,w,n=S.symbols('fm fp w n',nonzero=True)
    t=-n*w/(n*fm);assert S.simplify(w+fm*t-fp*t-(1+(fp-fm)*n/(n*fm))*w)==0
    # The above identity is componentwise valid with the common scalar t;
    # check a full 9D rank-one product using distinct symbolic components.
    f0=S.Matrix(S.symbols('f0:9'));f1=S.Matrix(S.symbols('p0:9'));W=S.Matrix(9,2,lambda i,j:S.Symbol('w%d_%d'%(i,j)))
    n=S.zeros(1,9);n[0,4]=1;dt=-n*W/f0[4]
    assert (W+f0*dt-f1*dt-(S.eye(9)+(f1-f0)*n/f0[4])*W).applyfunc(S.simplify)==S.zeros(9,2)
    return dict(status='PASS_EXACT_SWITCH_ALGEBRA_ONLY',diode_identity_events=[1,4,5,6],spark_rank_one_events=[2,3],original_source_interval_proof=False)


def consume(packet):
    import check_smith_filsinger_j31_native_seven_shortcharts_interval_20261124 as s
    import check_smith_filsinger_j35_conditional_lyapunov_geometry_20261125 as j35
    I=s.I; M0,P=j35.load_candidate(); q=F(1,20)
    def iv(x):return I(*x) if isinstance(x,list) else I(x)
    def mat(x):
        assert len(x)==9 and all(len(r)==9 for r in x)
        return [[iv(v) for v in r] for r in x]
    def vec(x):
        assert len(x)==9
        return [iv(v) for v in x]
    def mm(A,B):return [[sum((a*b for a,b in zip(r,c)),I(0)) for c in zip(*B)] for r in A]
    def rn(A):return max(sum(x.mag() for x in r) for r in A)
    def cn(A):return rn(list(zip(*A)))
    def dot(a,b):return sum((x*y for x,y in zip(a,b)),I(0))
    def ident():return [[I(int(i==j)) for j in range(9)] for i in range(9)]
    charts=packet['fixed_time_chart_jacobians']; events=packet['events'];assert len(charts)==7 and len(events)==6
    W=ident(); rows=[]
    for k,event in enumerate(events):
        W=mm(mat(charts[k]),W); X=vec(event['state_box']); t=iv(event['clock_box'])
        n=[0]*9;n[4]=1 if k in (1,2) else -1
        if k in (0,4):n[3]=1
        if k in (3,5):n[2]=1
        # Every candidate event state must intersect its exact named guard.
        h=s.guard(k,X);assert h.a<=0<=h.b
        if k in (1,2):X[4]=I(F('0.0018') if k==1 else F('0.006'))
        fm=s.f(X,t,s.MODES[k]); slope=s.guard_slope(k,fm)
        assert (slope.a>0 if s.SIGNS[k]>0 else slope.b<0),'nontransverse source event'
        L=iv(event['guard_left']);U=iv(event['guard_right'])
        assert (L.b<0<U.a if s.SIGNS[k]>0 else U.b<0<L.a),'no strict opposite signs'
        # Source left/right sign and no-extra-switch validity are premises,
        # not established by parsing these externally supplied intervals.
        nw=[dot([I(v) for v in n],list(c)) for c in zip(*W)]
        td=[-v/slope for v in nw]
        Xd=[[W[i][j]+fm[i]*td[j] for j in range(9)] for i in range(9)]
        delta=[I(0) for _ in range(9)]
        if k in (1,2):
            dc=s.MODES[k+1][2]-s.MODES[k][2];p=s.PARAM
            delta[4]=-dc*X[7]/p['Cb'];delta[7]=dc*(X[4]-p['Rgap']*X[7])/p['Lh']
        W=[[W[i][j]-delta[i]*td[j] for j in range(9)] for i in range(9)]
        lt=sum(v.mag() for v in td);lx=rn(Xd)
        tc=F(s.TIMES[k+1]);width=F(1,200000) if k<5 else F(1,5000)
        clock_ingress=(tc-width<t.a and t.b<tc+width)
        state_ingress=(all(F(c)-F(1,10000)<=x.a<=x.b<=F(c)+F(1,10000) for c,x in zip(s.STATES[k+1],X)) if k<5 else None)
        rows.append(dict(event=k+1,clock_derivative_upper=str(lt),state_derivative_upper=str(lx),
                         clock_budget=lt<=[10,20,20,10,4,40][k],state_budget=lx<=[50,150,150,10,10,10][k],
                         clock_box_ingress=clock_ingress,narrow_state_box_ingress=state_ingress))
    W=mm(mat(charts[6]),W); E=[[W[i][j]-M0[i][j] for j in range(9)] for i in range(9)]
    d=[v-F(c) for v,c in zip(vec(packet['centre_return_box']),s.STATES[0])]
    pnorm2=dot(d,[dot([I(x) for x in row],d) for row in P]);centre=pnorm2.b<F(1,10**20)
    derivative=rn(E)<=q and cn(E)<=q
    budgets=all(r['clock_budget'] and r['state_budget'] and r['clock_box_ingress'] and r['narrow_state_box_ingress'] is not False for r in rows)
    return dict(status='CONDITIONAL_INTERVAL_CONSUMER_ONLY',event_budgets=rows,
                D_return_error_1_upper=str(cn(E)),D_return_error_inf_upper=str(rn(E)),
                centre_P_squared_upper=str(pnorm2.b),centre_budget=centre,derivative_budget=derivative,
                numeric_inequality_budgets_pass=budgets and centre and derivative,
                original_source_array_provenance_validated=False,uniform_guard_chronology_proved=False,
                sixth_broad_source_ingress_proved=False,exact_periodic_orbit=False)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--packet',type=Path);p.add_argument('--self-test',action='store_true');a=p.parse_args()
    if a.self_test:print(json.dumps(self_test(),indent=2))
    elif a.packet:print(json.dumps(consume(json.loads(a.packet.read_text())),indent=2))
    else:p.error('source packet required, or --self-test')
