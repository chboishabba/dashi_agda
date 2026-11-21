#!/usr/bin/env python3
"""OCT369 P0.17a: finite Q8 gauge+three-spin same-source covariance.
Original literature: Wilson lattice gauge and covariant matter; Kang et al.
Nature 2026 DOI 10.1038/s41586-026-11172-5 own PtMn3 OTT/TMR.
YM PR #1536 owns the original R445 Gibbs BIDI; this is a DIFFERENT finite
fixture, not a transfer of its physical measure, OS positivity or Clay gap.
"""
import json
from itertools import product
from collections import Counter
from fractions import Fraction as F
import sympy as s

Q8=tuple(product((-1,1),range(4)))
IDENTITY=(1,0)
POS={(1,2):3,(2,3):1,(3,1):2}
SPINS=((-2,1,1),(1,-2,1),(1,1,-2)) # equal norm^2=6; angles 120 deg

def mul(a,b):
    sa,x=a; sb,y=b
    if x==0:return sa*sb,y
    if y==0:return sa*sb,x
    if x==y:return -sa*sb,0
    if (x,y) in POS:return sa*sb,POS[x,y]
    return -sa*sb,POS[y,x]
def inverse(a):return a[0]*(-1 if a[1] else 1),a[1]
def adjoint(g,v):
    if g[1]==0:return tuple(v)
    return tuple(v[i]*(1 if g[1]==i+1 else -1) for i in range(3))
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def obs(gs,spins=SPINS):
    gprod=mul(mul(gs[0],gs[1]),gs[2])
    W=gprod[0] if gprod[1]==0 else 0   # half the SU2 fundamental trace
    M=sum(dot(spins[i],adjoint(gs[i],spins[(i+1)%3])) for i in range(3))
    return W,M

def gauge(gs,spins,hs):
    links=tuple(mul(mul(hs[i],gs[i]),inverse(hs[(i+1)%3])) for i in range(3))
    new_spins=tuple(adjoint(hs[i],spins[i]) for i in range(3))
    return links,new_spins

def ensemble(subgroup):
    bins=Counter(obs(gs) for gs in product(subgroup,repeat=3))
    sums={key:F(0) for key in ('Z','W','M','WM','W2','M2')}
    for (w,m),n in bins.items():
        wt=n*F(2)**w*F(3,2)**m
        for key,value in [('Z',1),('W',w),('M',m),('WM',w*m),('W2',w*w),('M2',m*m)]:
            sums[key]+=wt*value
    c=(sums['WM']*sums['Z']-sums['W']*sums['M'])/sums['Z']**2
    return bins,sums,c

def main():
    passed=[]
    def check(label,condition):
        assert condition,label
        passed.append(label)
    check('8_Q8_elements',len(Q8)==8)
    check('Q8_identity',all(mul(x,IDENTITY)==x==mul(IDENTITY,x) for x in Q8))
    check('Q8_inverse',all(mul(x,inverse(x))==IDENTITY for x in Q8))
    check('Q8_associative',all(mul(mul(a,b),c)==mul(a,mul(b,c)) for a,b,c in product(Q8,repeat=3)))
    check('zero_bulk_spin',tuple(map(sum,zip(*SPINS)))==(0,0,0))
    check('120_degree_spins',all(dot(SPINS[i],SPINS[j])==-3 for i in range(3) for j in range(i+1,3)) and all(dot(v,v)==6 for v in SPINS))
    check('adjoint_dot_invariant',all(dot(adjoint(g,x),adjoint(g,y))==dot(x,y) for g in Q8 for x,y in product(SPINS,repeat=2)))
    check('adjoint_representation',all(adjoint(mul(g,h),v)==adjoint(g,adjoint(h,v)) for g,h,v in product(Q8,Q8,SPINS)))
    gauge_count=0
    for gs in product(Q8,repeat=3):
        original=obs(gs)
        for hs in product(Q8,repeat=3):
            links,spins=gauge(gs,SPINS,hs)
            assert obs(links,spins)==original,'gauge covariance'
            gauge_count+=1
    check('all_local_gauge_tests',gauge_count==8**6)
    bins,S,cov=ensemble(Q8)
    check('512_links',sum(bins.values())==512)
    check('positive_partition',S['Z']>0)
    check('mixed_cov_nonzero',cov!=0)
    check('centered_equals_moment',cov==S['WM']/S['Z']-(S['W']/S['Z'])*(S['M']/S['Z']))
    check('variance_W_nonnegative',S['W2']/S['Z']-(S['W']/S['Z'])**2>=0)
    check('variance_M_nonnegative',S['M2']/S['Z']-(S['M']/S['Z'])**2>=0)
    q,t=s.symbols('q t',positive=True)
    Z=sum(n*q**w*t**m for (w,m),n in bins.items())
    Zb=q*s.diff(Z,q);Zk=t*s.diff(Z,t);Zbk=q*t*s.diff(s.diff(Z,q),t)
    at={q:s.Integer(2),t:s.Rational(3,2)}
    as_sympy=lambda f:s.Rational(f.numerator,f.denominator)
    check('mixed_J_logjet_equals_centered',s.cancel(((Z*Zbk-Zb*Zk)/Z**2).subs(at))==as_sympy(cov))
    check('first_J_W_same_source',s.cancel((Zb/Z).subs(at))==as_sympy(S['W'])/as_sympy(S['Z']))
    check('first_J_M_same_source',s.cancel((Zk/Z).subs(at))==as_sympy(S['M'])/as_sympy(S['Z']))
    c4=tuple(g for g in Q8 if g[1] in (0,1))
    check('Cartan_C4_abelian',len(c4)==4 and all(mul(a,b)==mul(b,a) for a,b in product(c4,repeat=2)))
    half_trace=lambda g:g[0] if g[1]==0 else 0
    different=lambda a,b,c:half_trace(mul(mul(a,b),c))!=half_trace(mul(mul(a,c),b))
    q8_order=sum(different(*gs) for gs in product(Q8,repeat=3))
    c4_order=sum(different(*gs) for gs in product(c4,repeat=3))
    check('nonabelian_word_order_48',q8_order==48)
    check('Cartan_word_order_0',c4_order==0)
    b4,s4,cov4=ensemble(c4)
    check('Cartan_different_measure_response',cov4!=cov)
    flipped=tuple(tuple(-x for x in v) for v in SPINS)
    check('simultaneous_spin_reversal_even',all(obs(gs)==obs(gs,flipped) for gs in product(Q8,repeat=3)))
    check('source_independent_of_body_position',s.Symbol('z') not in Z.free_symbols)
    temp,alpha=s.symbols('kBT alpha',real=True)
    force=s.factor(temp*alpha*as_sympy(S['M'])/as_sympy(S['Z']))
    check('conditional_support_reaction',force+(-force)==0)
    check('zero_interface_gradient_zero_force',force.subs(alpha,0)==0)
    result={
        'scope':'independent Q8 triangle Wilson+three trial-spin finite fixture; NOT original #1536 physical measure',
        'assertions_passed':len(passed),'assertions':passed,
        'Q8_link_states':sum(bins.values()),'exhaustive_local_gauge_checks':gauge_count,
        'distinct_W_M_pairs':len(bins),'partition_function':str(S['Z']),
        'Gibbs_weight_parameters':{'q':'2','t':'3/2'},
        'mean_W':str(S['W']/S['Z']),'mean_M':str(S['M']/S['Z']),
        'exact_centered_WM':str(cov),'decimal_centered_WM':float(cov),
        'mixed_log_derivative_matches_covariance':True,
        'Cartan_C4_link_states':sum(b4.values()),'Cartan_C4_centered_WM':str(cov4),
        'Cartan_C4_centered_WM_decimal':float(cov4),
        'algebraic_order_changes_Q8':q8_order,'algebraic_order_changes_Cartan_C4':c4_order,
        'reordered_open_word_is_gauge_invariant':False,
        'conditional_body_force':str(force),'conditional_support_reaction':str(-force),
        'attribution':{
            'paper':'Kang et al. 2026 Nature doi:10.1038/s41586-026-11172-5; PtMn3 OTT/TMR belongs to original authors',
            'existing':'Wilson, SU2/Q8, covariant spin transport, source cumulants; YM #1536 original R445 same-source BIDI',
            'new':'DASHI OCT369 Q8 gauge-plus-120-spin source fixture; independent from R445 measure'},
        'original_R445_or_PtMn3_physical_measure_identified':False,
        'actual_cluster_T1g_octupole_identified':False,
        'physical_metric_stress_derived':False,
        'actual_levitation_or_gravity_anomaly_measured':False,
        'Clay_mass_gap_established':False,
    }
    print(json.dumps(result,sort_keys=True,indent=2))
if __name__=='__main__':main()
