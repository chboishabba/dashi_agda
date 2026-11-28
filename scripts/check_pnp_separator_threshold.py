"""Reproduce Section33 threshold-density cohort; compare opt-in allocations."""
from random import Random
from collections import Counter
from check_pnp_separator_portfolio import cnf_solver,prior
from check_pnp_frontier_resolution import accepts


def main():
    rng=Random(3693302);C=Counter()
    for n in (12,20,32,48):
        for planted in (False,True):
            for _ in range(8):
                w=tuple(rng.randrange(2) for i in range(n));F=[]
                for j in range(round(4.26*n)):
                    ids=rng.sample(range(n),3);c=tuple((i+1)*rng.choice((-1,1)) for i in ids)
                    if planted and not accepts((c,),w):c=(-c[0],)+c[1:]
                    F.append(c)
                F=tuple(F);q=prior(F,n,(),(),200000);z=cnf_solver(F,n,(),(),200000)
                if q['status']!='UNKNOWN' and z['status']!='UNKNOWN':assert q['status']==z['status']
                if z['status']=='WITNESS':assert accepts(F,z['witness'])
                if q['status']=='WITNESS':assert accepts(F,q['witness'])
                if planted:assert q['status']!='EMPTY' and z['status']!='EMPTY'
                C[n,q['status'],z['status']]+=1
    print(dict(C))
if __name__=='__main__':main()
