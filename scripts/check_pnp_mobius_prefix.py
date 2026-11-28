"""Transactional signed clause prefix with overlap-safe label mass tails.
All completed prefix histograms are exact on original Boolean lifts.
Logical work cap counts table probes and input/rank setup, not bit time.
"""
from itertools import product
from check_pnp_f3_syndrome_boundary import span,chart

class Refusal(Exception): pass

def prefix_contrast(F,cols,target,offset,R,w,term_cap=4096,work_cap=65536,chart_width=8,data_clock=None):
    R=tuple(sorted(R));n=len(R);r=len(target);full=(1<<n)-1
    st=dict(work=0,clauses=0,prefix=0,peak_terms=1,cube_queries=0,chart_points=0,dp_states=0)
    def measured_span(A,r):
        if data_clock is None:return span(A,r)
        from check_pnp_bit_data_schedule import span_bits,Refused as DataRefused
        try:return span_bits(A,r,data_clock)
        except DataRefused:raise Refusal()
    def measured_chart(A,b,r):
        if data_clock is None:return chart(A,b,r)
        from check_pnp_bit_data_schedule import chart_bits,Refused as DataRefused
        try:return chart_bits(A,b,r,data_clock)
        except DataRefused:raise Refusal()
    def pay(k):
        if st['work']+k>work_cap:raise Refusal()
        st['work']+=k
    def bits(m):
        while m:
            j=(m&-m).bit_length()-1;yield j;m^=1<<j
    def plus(a,b):return tuple((x+y)%3 for x,y in zip(a,b))
    def minus(a,b):return tuple((x-y)%3 for x,y in zip(a,b))
    def result(H,caps):
        lo=[];hi=[];total=sum(H);C=tuple(min(h,c) for h,c in zip(H,caps))
        for d,h in enumerate(H):
            v=3*h-total
            a=w*(v-2*C[d]);b=w*(v+sum(C[j] for j in range(3) if j!=d))
            lo.append(min(a,b));hi.append(max(a,b))
        return tuple(lo),tuple(hi),dict(st,head=H,removed_label_caps=C,exact=not any(C))
    try:
        # Reserve input and final suffix-scan charges before doing any work.
        pay(1+n+r+sum(5+len(c) for c in F))
        if () in F:return result((0,0,0),(0,0,0))
        B=measured_span((cols[j][:-1] for j in R),r);d=len(B)
        piv=tuple(next(i for i,a in enumerate(b) if a) for b in B);t=tuple(target[i] for i in piv)
        if tuple(sum(a*b[i] for a,b in zip(t,B))%3 for i in range(r))!=tuple(target):return result((0,0,0),(0,0,0))
        A=tuple(tuple(cols[j][i] for i in piv) for j in R);obs=tuple(cols[j][-1] for j in R);pos={j:i for i,j in enumerate(R)}
        cubes=set()
        for c in F:
            a=b=0
            for l in c:
                if l>0:a|=1<<pos[abs(l)-1]
                else:b|=1<<pos[abs(l)-1]
            if not a&b:cubes.add((a,b))
        cubes=sorted(cubes,key=lambda c:(-(c[0]|c[1]).bit_count(),c));st['clauses']=len(cubes)
        cache={}
        def hist(a,b):
            pay(1);key=(a,b)
            if key in cache:return cache[key]
            st['cube_queries']+=1;s=t;o=offset
            for j in bits(b):pay(1);s=minus(s,A[j]);o=(o+obs[j])%3
            I=tuple(bits(full^(a|b)));k=len(I);pay(1+k)
            # Small nullity alternative avoids a full syndrome table at high rank.
            rank=len(measured_span((A[j] for j in I),d));H=[0,0,0]
            if k-rank<=chart_width and 2**(k-rank)<3**d:
                q=measured_chart(tuple(tuple(A[j][i] for j in I) for i in range(d)),s,k)
                if q is not None:
                    u,V=q;pay(max(1,k)*2**len(V));st['chart_points']+=2**len(V)
                    for z in product(range(2),repeat=len(V)):
                        x=tuple((v+sum(c*b[i] for c,b in zip(z,V)))%3 for i,v in enumerate(u))
                        if 2 not in x:H[(o+sum(obs[j]*v for j,v in zip(I,x)))%3]+=1
            else:
                D={(0,)*d:(1,0,0)}
                for j in I:
                    pay(1+2*len(D));E=D.copy()
                    for v,h in D.items():
                        u=plus(v,A[j]);old=E.get(u,(0,0,0));E[u]=tuple(old[i]+h[(i-obs[j])%3] for i in range(3))
                    D=E;st['dp_states']+=len(D)
                h=D.get(s,(0,0,0));H=[h[(i-o)%3] for i in range(3)]
            cache[key]=tuple(H);return cache[key]
        M={(0,0):1};H=hist(0,0)
        # Each completed update is transactional; no partial signed map escapes.
        for a,b in cubes:
            try:
                pay(len(M));N=M.copy();removed=[0,0,0]
                for (p,q),c in M.items():
                    if p&b or q&a:continue
                    key=(p|a,q|b);v=N.get(key,0)-c
                    if v:N[key]=v
                    else:N.pop(key,None)
                    if len(N)>term_cap:raise Refusal()
                    h=hist(*key)
                    for i in range(3):removed[i]+=c*h[i]
                assert all(0<=v<=h for v,h in zip(removed,H))
                H=tuple(h-v for h,v in zip(H,removed));M=N;st['prefix']+=1;st['peak_terms']=max(st['peak_terms'],len(M))
                if not any(H):return result(H,(0,0,0))
            except Refusal:break
        caps=[0,0,0]
        # E_j=F_{j-1} intersect C_j are disjoint. Each label mass is
        # bounded by the WHOLE cube label count, not its character.
        for a,b in cubes[st['prefix']:]:
            try:h=hist(a,b)
            except Refusal:h=(2**(n-(a|b).bit_count()),)*3
            for i in range(3):caps[i]=min(H[i],caps[i]+h[i])
        return result(H,caps)
    except Refusal:return None


def prefix_portfolio(F,cols,target,offset,R,w,term_cap=4096,work_cap=65536,initial=1024,data_clock=None):
    """Geometric restart allowance with a shared total reservation.
    Every attempted cap is charged in full, even on refusal. This pays
    only declared logical work, not a physical bit-clock theorem.
    """
    if initial<=0 or work_cap<0:raise ValueError('budget')
    left=work_cap;size=initial;best=None;attempts=accepted=0
    while left:
        cap=min(size,left);left-=cap;attempts+=1
        q=prefix_contrast(F,cols,target,offset,R,w,term_cap,cap,data_clock=data_clock)
        if q is not None:
            accepted+=1;a,b,st=q
            if best is not None:a=tuple(max(x,y) for x,y in zip(a,best[0]));b=tuple(min(x,y) for x,y in zip(b,best[1]))
            assert all(x<=y for x,y in zip(a,b));best=(a,b,st)
            if a==b:break
        size*=2
    if best is None:return None
    a,b,st=best
    return a,b,dict(st,allocated=work_cap-left,attempts=attempts,accepted=accepted,exact_contrast=a==b)
