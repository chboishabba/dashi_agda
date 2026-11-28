"""Original Boolean-source Fourier probes, without a boundary-table oracle.
Classical F3 orthogonality and Parseval; DASHI source-specific attachment.
Disjoint CNF components on either side; bounded local Boolean enumeration.
No heavy-character discovery theorem is assumed.
"""
from itertools import product
from fractions import Fraction as Q
from math import isqrt
from check_pnp_f3_syndrome_boundary import blocks,span,dot,ceilroot

Z=(0,0);ONE=(1,0);OMEGA=((1,0),(0,1),(-1,-1))
def add(a,b):return a[0]+b[0],a[1]+b[1]
def mul(a,b):
    x,y=a;u,v=b
    return x*u-y*v,x*v+y*u-y*v

def norm(a):return a[0]*a[0]-a[0]*a[1]+a[1]*a[1]
def phase(a,d):return mul(a,OMEGA[d%3])
def contrast(a):
    x,y=a;return 2*x-y,2*y-x,-x-y


def dual_contrast(F,cols,target,offset,R,w,local_width=6,probe_cap=32,work_cap=16384):
    """Return directional interval and certificate, or None on refusal.
    Fourier normalization is 3^-r over the actual affine equation carrier.
    If both side images are full, this IS the intrinsic boundary dual.
    Local point probes/character summands charged; bit/RREF costs separate.
    """
    R=tuple(sorted(R));r=len(target);q=3**r;work=0
    if () in F:return (Q(0),)*3,(Q(0),)*3,dict(work=0,probes=0,exact=True)
    G=blocks(F,R)
    if len(G)<2 or probe_cap<=0:return None
    side=[];nside=[];energies=[];ranks=[]
    for subset in (G[:len(G)//2],G[len(G)//2:]):
        tables=[];N=1;E=1;rank_sum=0;allcols=[];n=0
        for I,C in subset:
            if len(I)>local_width:return None
            work+=2**len(I)
            if work>work_cap:return None
            H={};n+=len(I);A=tuple(cols[j][:-1] for j in I);allcols.extend(A)
            rank_sum+=len(span(A,r));count=0
            for bits in product(range(2),repeat=len(I)):
                x=dict(zip(I,bits))
                if not all(any(x[abs(l)-1]==int(l>0) for l in cl) for cl in C):continue
                s=tuple(sum(cols[j][a]*x[j] for j in I)%3 for a in range(r))
                o=sum(cols[j][-1]*x[j] for j in I)%3
                H[s]=add(H.get(s,Z),OMEGA[o]);count+=1
            N*=count;E*=sum(norm(a) for a in H.values());tables.append(H)
        rank=len(span(allcols,r));ranks.append(rank);nside.append(N)
        # Direct-sum syndrome images imply unique splitting of each local
        # label, so collision energy multiplies. Otherwise use the Boolean
        # free-coordinate cap on every syndrome fibre, never F3 volume.
        if rank_sum!=rank:E=N*min(N,2**(n-rank))
        energies.append(q*E);side.append(tables)
    if not all(nside):return (Q(0),)*3,(Q(0),)*3,dict(work=work,probes=0,exact=True)
    # Deterministic probes: no claim that omitted modes are light.
    def candidates():
        if q<=probe_cap:yield from product(range(3),repeat=r);return
        yield (0,)*r
        for j in range(r):
            for a in (1,2):yield tuple(a if i==j else 0 for i in range(r))
    head=Z;seen=0;EL,ER=energies
    cost=1+sum(len(H) for tables in side for H in tables)
    for y in candidates():
        if seen>=probe_cap or work+cost>work_cap:break
        work+=cost;seen+=1;vals=[]
        for tables in side:
            z=ONE
            for H in tables:
                v=Z
                for s,a in H.items():v=add(v,phase(a,dot(s,y)))
                z=mul(z,v)
            vals.append(z)
        a,b=vals;EL-=norm(a);ER-=norm(b)
        assert EL>=0 and ER>=0
        head=add(head,phase(mul(a,b),offset-dot(y,target)))
        if not EL or not ER:break
    # If every mode was queried there is no omitted term even when
    # the independently supplied energy bound was loose.
    err=0 if seen==q else ceilroot(EL*ER)
    h=tuple(Q(w*a,q) for a in contrast(head));radius=2*abs(w)*Q(err,q)
    return tuple(a-radius for a in h),tuple(a+radius for a in h),dict(work=work,probes=seen,dual_rank=r,side_ranks=ranks,source_mass=nside,initial_energy=energies,omitted_energy=[EL,ER],error_numerator=err,normalizer=q,head=head,exact=err==0)
