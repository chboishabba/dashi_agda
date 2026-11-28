"""Original F8 cap: finite signed path hierarchy and geometric delay budget.
Conditional on existing smooth layer/causal equivalence; no total sign claim.
"""
from fractions import Fraction as Q
import json
import sympy as S
from check_f8_cap_all_frequency import root,clock,direction
from check_f8_global_wall_kernel import Fbox


def run():
    checks=0
    def check(x):
        nonlocal checks
        assert x;checks+=1
    eps=Q('.04');rho=Q('.000361');umin=1-rho/eps
    check(umin>Q('.99'));check(1/(1-umin*umin)>55)
    # Reuse signed radial recurrence, strengthen the chart to X>=55.
    X,Y=S.symbols('X Y');P=S.Poly(1,X);p=1;polys=[];shifted=[];slope=10000
    for j in range(19):
        r=S.Poly((-1)**j*P.as_expr(),X);polys.append(r)
        sh=S.Poly(r.as_expr().subs(X,Y+55),Y);shifted.append(sh)
        if j<=17:
            check(min(sh.all_coeffs())>0)
            if j:check(min((sh-S.Rational(slope*4,99)*shifted[j-1]).all_coeffs())>=0)
        P=S.Poly(P.as_expr()+2*(X*X-X)*(P.diff().as_expr()-P.as_expr()) if p else 2*X*X*(P.diff().as_expr()-P.as_expr()),X);p=1-p
    # Self block nonnegative coefficients inherited, and cross angle sign on actual path.
    hE,hR=Q('.0037'),Q('.01');Lmax=Q('2.66');bE,bR=Q('.997'),Q('.087')
    crossdr=Q('2.49')-hE-hR;check(crossdr>Q('.9')*Lmax)
    gain=slope*Q('.9')/Lmax-Q(15,8)/(bE*bR);check(gain>0)
    for h,b,a in ((hE,bE,Q('.26')),(hR,bR,Q('.09'))):
        check(Q(5,4)-Q(15,8)*a*h*h/(2*b)>0)
    # Each self interaction costs two signed derivatives, one cross costs one.
    M=5;check(6+2*M+1==17)
    terms=[('direct',0,j) for j in range(M+1)]+[('cross',i,j) for i in range(M+1) for j in range(M+1-i)]
    check(len(terms)==27)
    # Exact noncommutative remainder at any finite triangular cut, both clocks retained.
    E,R,C,U,W=S.symbols('E R C U W',commutative=False)
    a=U-E*U;b=W-R*W-C*U
    for m in range(7):
        P=sum(R**j*b for j in range(m+1))+sum(R**j*C*E**i*a for i in range(m+1) for j in range(m+1-i))
        residual=R**(m+1)*b+sum(R**(m+1-i)*C*E**i*a for i in range(m+1))+C*E**(m+1)*U
        check(S.expand((1-R)*(W-P)-residual)==0)
    # Exact support-function excess budget, including summed self-leg times.
    f=Fbox(Q(1));g=Fbox(Q(1,12));span=(g[0]-f[1],g[1]-f[0]);T=(span[0]-Q('.05'),span[1]-Q('.05'))
    rlo=root(span[0]**2-Q(11,12)**2)[0]-Q('.012');rhi=root(span[1]**2-Q(11,12)**2)[1]-Q('.012')
    check(rlo-eps>Q('2.49'));check(2<rlo<rhi<3);check(T[1]<Lmax)
    be=(Q('.087590020348'),Q('.087590020352'));check(Fbox(be[0])[0]>g[1]-Q('.05') and Fbox(be[1])[1]<g[0]-Q('.05'))
    u,c=direction(Q('-.177'));check(u*u+c*c==1 and c>0 and u<0)
    reach=(T[1]-u*(be[1]-1))/c-rlo+eps;check(reach<rho)
    check(Q('.708')**2>Q(1,2))
    check((1+u*Q('.708'))/c>Q('.8'));check((1+u*Q('.09'))/c>Q('1.03'))
    # Mean wall velocities in E<=-.7 and R>=-.09 by original clock collar guards.
    check(bE*bE>Q('.7')**2/(1-Q('.7')**2));check(Q('.09')**2/(1+Q('.09')**2)<Q('.09')**2)
    # phi(w)=(1-u w)/c-sqrt(1-w²) convex, minimum at u.
    delay=[]
    for w,z in ((Q('-.7'),Q('.09')),(Q('-.09'),Q('.035'))):
        low=(1-u*w)/c-root(1-w*w)[1];check(low>z);delay.append(float(low))
    L,Z,V,H=S.symbols('L Z V H',real=True)
    check(S.expand((L-V*Z)**2-(1-V*V)*(L*L-Z*Z)-(Z-V*L)**2)==0)
    # Joint exponential lower on raw bump exponents by weighted CS.
    roots=list(map(Q,['.1140','.2269','.1414']))
    for r,w in zip(roots,(Q('.8')*Q('.065')/4,Q('1.03')*Q('.05'),eps/2)):check(r*r<w)
    K=sum(roots)**2;base=K/rho;rateE=K/rho**2*Q('.09');rateR=K/rho**2*Q('.035')
    check(base>644);check(rateE>160000);check(rateR>62000)
    # Negative control: actual interior causal source, not just a loose chart.
    s=d=Q('.0000001');depth=Q('.000358');bs=clock(s,f);br=(clock(T[1]-d,f)[0],clock(T[0]-d,f)[1]);qlo=(T[0]-s-d)**2-(bs[1]-br[0])**2-(rhi-eps+depth)**2
    check(qlo>0);uu=1-depth/eps;xx=1/(1-uu*uu)
    check(polys[18].eval(S.Rational(xx))<0)
    # Actual D partial_rr source payload, twelfth signed derivative: orders 14..18.
    vals=[Q(polys[j].eval(S.Rational(xx)))*uu**(1-j%2)*eps**(5-j) for j in range(14,19)]
    upper=sum(max(Q(0),vals[j])*Q(w,2**(5-j)) for j,w in enumerate((3,3,3,2)))+vals[4]/3
    check(upper<0)
    return dict(checks=checks,source_X_lower=float(1/(1-umin*umin)),certified_derivative_orders=list(range(18)),log_slope_lower=slope,cross_radial_separation_lower=float(crossdr),cross_gain_over_N_lower=float(gain),self_order=M,selected_direct=M+1,selected_cross=(M+1)*(M+2)//2,selected_total=len(terms),residual_noncommutative_checks=7,delay=dict(direction=[str(u),str(c)],available_budget_upper=str(rho),actual_support_upper_display=float(reach),emission_rate_lower='.09',reception_rate_lower='.035',time_weights=['.8','1.03'],support_delay_lower=delay,raw_exponent_base_lower=float(base),raw_exponent_self_time_rates=[float(rateE),float(rateR)]),negative_control=dict(source_elapsed=float(s),receiver_before_end=float(d),depth=float(depth),q_lower=float(qlo),X=float(xx),signed_order18_negative=True,actual_Drr_payload_signed_order12_negative=True,upper_relative_to_abs_last=float(upper/abs(vals[4]))),scope='conditional finite selected sign hierarchy and raw exponential path-delay budget; no all-orders cone, full receiver interval, or differentiated remainder bound')

if __name__=='__main__':print(json.dumps(run(),indent=2))
