"""Exact whole-configuration recurrence on the original parsed stack emitter.
Acceleration is a representation algorithm, not a same-target tape execution.
"""
from check_pnp_stack_fractran import compile_candidate_bits, source_next
from check_pnp_stack_priority_transport import AuditedRunner
from check_pnp_candidate_literal_endpoint import candidate_bits


def periodic(M,start,steps,macro_cap,exponent_cap=4096):
    if min(steps,macro_cap,exponent_cap)<0:raise ValueError('bounds')
    A=AuditedRunner(M);v=start;j=raw=executed=skipped=0;seen={};periods=[]
    while j<steps:
        if max(v[:5]).bit_length()>exponent_cap:
            return dict(status='UNKNOWN',steps=j,raw=raw,executed=executed)
        if v in seen:
            k,c=seen[v];p=j-k;d=raw-c
            assert p>0 and d>0
            cycles=(steps-j)//p
            if cycles:
                j+=cycles*p;raw+=cycles*d;skipped+=cycles*p
                periods.append((k,p,d,cycles))
                if j==steps:break
        else:seen[v]=(j,raw)
        if executed==macro_cap:
            return dict(status='UNKNOWN',steps=j,raw=raw,executed=executed)
        q,L,R,h=M.decode(v);want=source_next(M,(q,L,R))
        if h or want is None:
            return dict(status='EARLY_HALT',steps=j,raw=raw,executed=executed)
        u,h,c=A.exact(v,True)
        assert not h and M.decode(u)==(*want,False)
        v=u;j+=1;raw+=c['raw'];executed+=1
    return dict(status='ENDPOINT',state=v,steps=j,raw=raw,executed=executed,
                skipped=skipped,periods=tuple(periods))


def main():
    from itertools import product
    from collections import Counter
    C=Counter()
    for blank,b,c in product(range(2),repeat=3):
        rules=tuple((q,a,1-q,b if q==0 else c,0) for q,a in product(range(2),repeat=2))
        M,_,_=compile_candidate_bits(2,2,len(rules),candidate_bits(2,2,blank,0,1,rules))
        for left,right in product(((),(blank,)),((0,),(1,),(blank,0))):
            start=M.encode(0,left,right);v=start;raw=0;A=AuditedRunner(M)
            for T in range(25):
                z=periodic(M,start,T,4)
                assert z['status']=='ENDPOINT' and z['state']==v and z['raw']==raw
                C['finite_endpoints']+=1
                v,h,cost=A.exact(v,True);assert not h;raw+=cost['raw']
            T=10**60+1;z=periodic(M,start,T,4)
            assert z['status']=='ENDPOINT' and z['skipped']>=T-4 and z['steps']==T
            C['huge_periodic']+=1
    # Same rule at every step, but no repeated full configuration:
    # the left tape extent grows, including explicit blank cells.
    rules=((0,0,0,0,1),)
    M,_,_=compile_candidate_bits(1,1,1,candidate_bits(1,1,0,0,0,rules))
    z=periodic(M,M.encode(0,(),(0,)),100,8)
    assert z['status']=='UNKNOWN' and z['executed']==8
    C['template_not_state']=1
    print(dict(C))
if __name__=='__main__':main()
