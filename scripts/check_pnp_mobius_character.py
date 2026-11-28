"""Signed clause-intersection contraction on an original Boolean source.

Inclusion-exclusion is on falsifying partial assignments, with inconsistent
intersections discarded and identical intersections combined. The remaining
cube characters use low-rank syndrome DP, not enumeration of Boolean lifts.
All table construction and cube queries are bounded; refusal is not zero.
"""
from check_pnp_f3_syndrome_boundary import span
from check_pnp_dual_syndrome_fourier import Z, ONE, OMEGA, add, mul, phase, contrast


class Refusal(Exception):pass


def mobius_contrast(F,cols,target,offset,R,w,rank_cap=4,term_cap=4096,work_cap=65536):
    R=tuple(sorted(R));n=len(R);r=len(target);stats=dict(work=0,rank=0,terms=0,peak_terms=1,cube_states=0,cache_hits=0)
    def pay(k):
        if stats['work']+k>work_cap:raise Refusal('work')
        stats['work']+=k
    def result(z):
        a=tuple(w*t for t in contrast(z));return a,a,dict(stats,character=z)
    try:
        pay(1+n+r+sum(1+len(c) for c in F))
        if () in F:return result(Z)
        B=span((cols[j][:-1] for j in R),r);d=len(B);stats['rank']=d
        piv=tuple(next(i for i,a in enumerate(b) if a) for b in B)
        t=tuple(target[i] for i in piv)
        if tuple(sum(a*b[i] for a,b in zip(t,B))%3 for i in range(r))!=tuple(target):return result(Z)
        if d>rank_cap or term_cap<1:raise Refusal('rank/terms')
        pos={j:i for i,j in enumerate(R)};A=tuple(tuple(cols[j][i] for i in piv) for j in R);obs=tuple(cols[j][-1] for j in R)
        def plus(a,b):return tuple((x+y)%3 for x,y in zip(a,b))
        def minus(a,b):return tuple((x-y)%3 for x,y in zip(a,b))
        cubes=set()
        for c in F:
            zero=one=0
            for l in c:
                bit=1<<pos[abs(l)-1]
                if l>0:zero|=bit
                else:one|=bit
            if not zero&one:cubes.add((zero,one))
        # Union of forbidden cubes: a smaller pin set subsumes a larger
        # consistent pin set. Charge every subsumption comparison.
        kept=[]
        for z,o in sorted(cubes,key=lambda p:((p[0]|p[1]).bit_count(),p)):
            dominated=False
            for a,b in kept:
                pay(1)
                if a&z==a and b&o==b:dominated=True;break
            if not dominated:kept.append((z,o))
        M={(0,0):1}
        for z,o in kept:
            pay(len(M));N=M.copy()
            for (a,b),c in M.items():
                if a&o or b&z:continue
                p=(a|z,b|o);v=N.get(p,0)-c
                if v:N[p]=v
                else:N.pop(p,None)
                if len(N)>term_cap:raise Refusal('term cap')
            M=N;stats['peak_terms']=max(stats['peak_terms'],len(M))
            if not M:return result(Z)
        stats['terms']=len(M);full=(1<<n)-1;cache={0:{(0,)*d:ONE}}
        def bits(m):
            while m:
                j=(m&-m).bit_length()-1;yield j;m^=1<<j
        def table(mask):
            pending=[];m=mask
            while m not in cache:
                j=(m&-m).bit_length()-1;pending.append((m,j));m^=1<<j
            stats['cache_hits']+=1;D=cache[m]
            for m,j in reversed(pending):
                pay(1+2*len(D));E=D.copy()
                for s,a in D.items():
                    u=plus(s,A[j]);E[u]=add(E.get(u,Z),phase(a,obs[j]))
                D={s:a for s,a in E.items() if a!=Z};cache[m]=D;stats['cube_states']+=len(D)
            return D
        out=Z
        for (a,b),c in M.items():
            pay(1+b.bit_count());s=t;o=offset
            for j in bits(b):s=minus(s,A[j]);o+=obs[j]
            v=phase(table(full^(a|b)).get(s,Z),o)
            out=add(out,(c*v[0],c*v[1]))
        return result(out)
    except Refusal:return None
