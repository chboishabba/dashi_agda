"""Full-horizon rational reflection-box negative controls and signed memory."""
from fractions import Fraction as F
from solar_passive_campaign_bound import rational_reflection_enclosure

h=F(1,3)
source=[F(1),-F(1,2),F(1,4),F(0)]
def run(load,fixed):
    x=y=F(0); reflected=F(0); trace=[]
    for i,inc in enumerate(source):
        applied=F(1,2) if fixed and i==3 else load
        mid=(x+h*inc)/(1+h*(applied+1)/2)
        reflected+=h*(mid-inc)**2
        report_error=F(-1 if i%2 else 1,10000)
        trace.append(dict(edge_midpoint=[str(mid+report_error),str(y)],
            midpoint_error=[str(abs(report_error)),'0'],
            incident=str(inc),terminal=i==3,
            reflected=str(mid-inc)))
        x=2*mid-x
        x,y=(3*x-4*y)/5,(4*x+3*y)/5
    return reflected,trace

results=[]
for fixed in (False,True):
    _,trace=run(F(1,2),fixed)
    result=rational_reflection_enclosure(trace,
        ['1/2','0'],['2/5','0'],['3/5','0'],str(h),'1',0,fixed)
    bound=F(result['reflection_lower_exact'])
    assert bound>0
    for j in range(101):
        lam=F(2,5)+F(j,500)
        reflected,_=run(lam,fixed)
        assert reflected>=bound,(fixed,j,reflected,bound)
    results.append(dict(fixed_terminal=fixed,
        reflection_lower_exact=str(bound),sampled_cases=101))
print(dict(status='PASS',cases=202,results=results))
