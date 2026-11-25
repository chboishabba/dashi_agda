"""Reverse solve actual fixed F8 window support; no propagated-field bound.
Reuse original rational clock Fbox. All accepted inequalities exact rational.
"""
from fractions import Fraction as Q
from math import isqrt
import json
from check_f8_global_wall_kernel import Fbox

def root(x):
    d=10**18;n=isqrt((x*d*d).numerator//(x*d*d).denominator)
    return Q(n,d),Q(n+1,d)

def sub(a,b):return a[0]-b[1],a[1]-b[0]
def shift(a,b):return a[0]+b,a[1]+b

def bracket(target,lo,hi):
    lo,hi=Q(lo),Q(hi)
    assert Fbox(lo)[0]>target[1] and Fbox(hi)[1]<target[0]
    return lo,hi

def run():
    eps=Q(1,25);s=Q(9,20000);d=Q(7,20000);F1=Fbox(Q(1));F12=Fbox(Q(1,12));span=sub(F12,F1);end=shift(span,-Q(1,20));early=shift(end,-d)
    # Rational bracket proposals, verified against original decreasing clock.
    be=bracket(shift(F12,-Q(1,20)),'.087590020348','.087590020352')
    bc=bracket(shift(F12,-Q(1,20)-d),'.087620000','.087622000')
    bs=bracket(shift(F1,s),'.999681000','.999683000')
    rr=(root(span[0]**2-Q(11,12)**2)[0]-Q(3,250),root(span[1]**2-Q(11,12)**2)[1]-Q(3,250))
    earlygap=early[1]**2-(1-bc[1])**2-(rr[0]-eps)**2
    lategap=(end[1]-s)**2-(bs[0]-be[1])**2-(rr[0]-eps)**2
    assert earlygap<0 and lategap<0
    reach=(root(end[0]**2-(1-be[0])**2)[0],root(end[1]**2-(1-be[1])**2)[1]);rho=(reach[0]-rr[1]+eps,reach[1]-rr[0]+eps)
    assert 0<rho[0]<=rho[1]<Q(361,10**6)
    assert rr[0]-reach[1]>Q(396,10000)
    # Along actual lens, |v_source|<=1/sqrt(2), receiver b<.1.
    # -D_s,D_t >= sqrt(1-v^2), by the exact square identity below.
    alpha,beta=Q(7,10),Q(99,100)
    assert alpha**2<Q(1,2) and beta**2<1/(1+bc[1]**2)
    a,b,c=Q(13,200)/4,Q(1,5)/4,eps/2
    p,q,r=Q('0.1066'),Q('0.2224'),Q('0.1414')
    assert p*p<a*alpha and q*q<b*beta and r*r<c
    X=(p+q+r)**2/Q(361,10**6)
    assert X>612
    # e > 27/10 from first six terms of exp(1); product exp(3-X).
    from math import factorial
    assert sum((Q(1,factorial(j)) for j in range(6)),Q(0))>Q(27,10)
    assert Q(10,27)**609<Q(1,10**262)
    # Original 4516-interval modal clock: no integer sample lies in either cap.
    n=4516;j=4432;gap=(span[0]*Q(n-j,n)-Q(1,20),span[1]*Q(n-j,n)-Q(1,20))
    assert gap[0]>d and gap[1]<span[0]/n and span[0]/n>s
    # Strictly positive support-overlap witness, not a signal-sign proof.
    sw=Q(1,20000);dw=Q(1,20000);rw=Q(399,10000)
    bwe=bracket(shift(F1,sw),'.999964000','.999966000')
    bwr=bracket(shift(F12,-Q(1,20)-dw),'.087593000','.087596000')
    witness=(end[0]-dw-sw)**2-(bwe[1]-bwr[0])**2-(rr[1]-rw)**2
    assert witness>0
    import sympy as S
    L,Z,v=S.symbols('L Z v');assert S.expand((L-Z*v)**2-(1-v*v)*(L*L-Z*Z)-(Z-L*v)**2)==0
    # For nonnegative s,d,delta, each exponent >= a/s,b/d,c/delta;
    # Cauchy gives sum >= (sqrt(a alpha)+sqrt(b beta)+sqrt(c))^2/rho.
    def box(x):return [float(v) for v in x]
    return dict(scope='exact rational causal cap conditional on original smooth-reference finite propagation; raw bump products only, no propagated-field or sign bound',span=box(span),receiver_end=box(end),receiver_b=box(be),earliest_allowed_offset_upper=float(d),source_elapsed_upper=float(s),source_radius_lower=.0396,early_receiver_squared_gap_upper=float(earlygap),late_source_squared_gap_upper=float(lategap),radial_margin=box(rho),strict_support_witness_squared_gap_lower=float(witness),joint_exponent_lower=float(X),integer_time_grid=dict(intervals=n,last_window_node=j,last_node_to_window_end=box(gap),step=box((span[0]/n,span[1]/n)),source_and_receiver_caps_have_no_interior_integer_nodes=True,stage_and_stencil_caveat=True),raw_bump_product_upper='1e-262',checks='exact rational inequalities and symbolic characteristic derivative square',notes='Window center span-.15, half-width .10, source duration .065, radius .04; original near receiver r=sqrt(span^2-(11/12)^2)-.012. Both endpoint bumps flat; strict interior overlap remains.')
if __name__=='__main__':print(json.dumps(run(),indent=2))
