#!/usr/bin/env python3
"""Original -log finite two-sided increment and dyadic eta shortcut.

For m>=1 and LN(m)=sum_(j=1)^N ((m-1)/m)^j/j:
 (1-((m-1)/m)^N)/(m+1) <= LN(m+1)-LN(m)
 <= (1-(m/(m+1))^N)/m.
After the actual Bishop limit/order weld:
 1/(m+1)<=L(m+1)-L(m)<=1/m,
 L(2m)-L(m)>=1/2, L(2^k)>=k/2.
Then for Re(s)>=delta>0, |s|<=R, q=exp(-delta/2)<1,
 arbitrary alternating tail N>=2^K:
 |tail|<=(1+R*exp(R)/(1-q))*q^K,
 once native complex expC difference and norm bounds are proved.
No continuous real-axis FTC or dyadic Nat-log EQUALITY needed for
this eta convergence route. THIS IS NOT A BISHOP KERNEL RECEIPT.
"""
from fractions import Fraction as Q
import cmath,math,json

def part(m,N):
    x=Q(m-1,m)
    return sum((x**j/Q(j) for j in range(1,N+1)),Q(0))

def check():
    finite=0
    for m in range(1,71):
        a,b=Q(m-1,m),Q(m,m+1)
        for N in range(1,46):
            v=part(m+1,N)-part(m,N)
            assert 0<(1-a**N)/Q(m+1)<=v<=(1-b**N)/Q(m)
            finite+=1
    shells=0
    for m in range(1,65):
        assert sum((Q(1,n+1) for n in range(m,2*m)),Q(0))>=Q(1,2)
        shells+=1
    dyadic=0
    for k in range(15):
        assert sum((Q(1,n+1) for n in range(1,2**k)),Q(0))>=Q(k,2)
        dyadic+=1
    numerical=0
    for s in (complex(.5,0),complex(.5,3),complex(.75,2),complex(1.25,4)):
        q=math.exp(-s.real/2);R=abs(s)
        for K in range(7):
            C=(1+R*math.exp(R)/(1-q))*q**K
            for N in (2**K,2**K+1,2**K+5):
                for M in (N,N+3,N+15):
                    v=sum(((-1)**(n-1)*cmath.exp(-s*math.log(n))
                           for n in range(N,M+1)))
                    assert abs(v)<=C*(1+1e-11)
                    numerical+=1
    return {'schema':'bishop-original-natlog-two-sided-dyadic-v1',
      'result':'PASS','exact_two_sided_increment_cases':finite,
      'exact_dyadic_shell_cases':shells,'exact_geometric_dyadic_cases':dyadic,
      'non_Bishop_complex_numeric_checks':numerical,
      'increment_target':'1/(m+1)<=L(m+1)-L(m)<=1/m',
      'dyadic_target':'L(2^k)>=k/2',
      'uniform_tail_target':'(1+R*exp(R)/(1-q))*q^K',
      'q':'exp(-delta/2)',
      'continuous_FTC_required':False,'dyadic_log_equality_required':False,
      'original_Bishop_order_limit_proved':False,
      'original_complex_exp_difference_and_norm_proved':False,
      'original_eta_uniform_convergence_kernel':False}
if __name__=='__main__':print(json.dumps(check(),indent=2))
