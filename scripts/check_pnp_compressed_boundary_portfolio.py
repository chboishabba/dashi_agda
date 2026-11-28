"""Original CNF/one-hot compression; explicit route selection, no default change."""
from itertools import combinations
from check_pnp_prime_power_incidence import exact_rows,incidence
from check_pnp_frontier_resolution import accepts,norm
from check_pnp_source_derived_cover import Reservation,Refused
from check_pnp_normal_mass import count
from check_pnp_affine_accumulator import solve


def extract(F,n,B):
    O=exact_rows(F,n,B);owned=set()
    for c in O:
        B.pay(1+len(c)**2);owned.add(tuple(j+1 for j in c))
        owned.update(norm((-i-1,-j-1)) for i,j in combinations(c,2))
    B.pay(1+sum(1+len(c) for c in F));return tuple(c for c in F if norm(c) not in owned),O


def original(F,n,cap,route='normal',clip=2):
    B=Reservation(cap)
    try:
        G,O=extract(F,n,B);B.pay(1+n+sum(1+len(c) for c in G+O))
        if route=='normal':
            H=tuple((sum(1<<j for j in c),1) for c in O)
            flats=tuple(tuple((1<<(abs(l)-1),int(l<0)) for l in c) for c in G)
            ones=tuple(tuple((1<<j,0) for j in c) for c in O)
            q=count(n,H,flats,ones,B.left,clip)
            if q['status']=='WITNESS':q=dict(q,witness=tuple(q['witness']>>j&1 for j in range(n)))
        elif route=='rational':
            B.pay(1+len(O)*(n+1));A,b=incidence(O,n)
            q=solve(A,b,n,G,cap=B.left,clip=clip)
        else:raise ValueError('route')
        B.pay(q['used'])
        if q['status']=='WITNESS':
            B.pay(1+n+sum(1+len(c) for c in F));assert accepts(F,q['witness'])
        return dict(q,reserved=cap-B.left,route=route,rows=len(O),remaining=len(G))
    except Refused:return dict(status='UNKNOWN',reserved=cap-B.left,route=route)


def guarded(F,n,cap,route):
    from check_pnp_guarded_resolution_boundary import guarded as make,restrict_clause
    B=Reservation(cap)
    try:B.pay(1+3*n+sum(2+len(c) for c in F))
    except Refused:return dict(status='UNKNOWN',reserved=cap-B.left)
    H,G=make(F,n);anchor=(0,)*(n+1);assert accepts(H,anchor)
    R=tuple(r for c in G if (r:=restrict_clause(c,{n:1})) is not None);assert R==tuple(map(norm,F))
    q=original(R,n,B.left,route);used=cap-B.left+q['reserved']
    if q['status']=='EMPTY':return dict(status='COMPLETE',count=1,witness=anchor,reserved=used)
    if q['status']=='WITNESS':
        x=q['witness']+(1,);assert accepts(G,x);return dict(status='COMPLETE',count=2,witness=anchor,other=x,reserved=used)
    return dict(status='UNKNOWN',witness=anchor,lower=1,upper=2,reserved=used)


def main():
    from itertools import product
    from random import Random
    rng=Random(3693603);checks=0
    for n in range(1,9):
        for _ in range(24):
            O=tuple(tuple(j for j in range(n) if rng.randrange(2)) for i in range(rng.randrange(4)))
            F=tuple(tuple(j+1 for j in c) for c in O)+tuple((-i-1,-j-1) for c in O for i,j in combinations(c,2))
            F+=tuple(tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for j in range(3)) for i in range(2))
            W=[x for x in product((0,1),repeat=n) if accepts(F,x)]
            for route in ('normal','rational'):
                q=original(F,n,10**7,route,clip=None);assert q['count']==len(W)
                if W:assert q['witness'] in W
                g=guarded(F,n,10**7,route);assert g['count']==(2 if W else 1);checks+=1
    for n in (16,32,64,128):
        F=(tuple(range(1,n+1)),)+tuple((-i,-j) for i,j in combinations(range(1,n+1),2))
        for route in ('normal','rational'):
            q=original(F,n,10**8,route,clip=None);assert q['count']==n and q['remaining']==0 and q['rows']==1
            print('original',n,route,q['reserved'],q.get('peak',q.get('width')))
    for route in ('normal','rational'):
        assert original(((1,),),1,0,route)['status']=='UNKNOWN'
        assert guarded(((1,),),1,0,route)['status']=='UNKNOWN'
    print('original exact and guarded route pairs',checks,'refusals PASS')
if __name__=='__main__':main()
