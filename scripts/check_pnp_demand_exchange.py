"""One shared ledger/clock for direct cover and rooted monotone exchange."""
from check_pnp_affine_normal_components import satisfies
from check_pnp_demand_strata import Ledger,Allowance,ProbeLimit,solve_cover,rooted_probe


def descent(n,R,P,x,B,leaf_cap=8,seam_cap=8,nodes=32,probe_cap=1000000,
            donor_depth=1,character_degree=-1,cell_cap=128,history=None,k_index=0):
    assert len(R)%3==0 and all(sum(r>>j&1 for r in R)==3 for j in range(n))
    assert satisfies(x,P,())
    k=len(R)//3;L=Ledger(n,R,P);t=0
    if x.bit_count()==k:
        assert all((r&x).bit_count()==1 for r in R);return x,True
    # Direct-cover demands are incumbent-independent: do not repeat this phase.
    if nodes:
        y,done=solve_cover(n,R,P,B,leaf_cap,seam_cap,nodes,probe_cap,donor_depth,character_degree,cell_cap,L)
        if done:
            if y is not None and y!=x and history is not None:
                q=tuple((r&x).bit_count()-(r&y).bit_count() for r in R)
                assert all(a>=0 and a%2==0 for a in q) and any(q)
                history.append((k_index,t,x,x^y,q,B.left))
            return y,True
    while x.bit_count()>k:
        unknown=False;v=None
        for e,r in enumerate(R):
            if (r&x).bit_count()==1:continue
            B.pay('demand_exchange_root')
            try:status,c,v=rooted_probe(L,x,e,(),Allowance(B,probe_cap),leaf_cap,seam_cap,cell_cap,character_degree)
            except ProbeLimit:unknown=True;continue
            if v is not None:break
            unknown|=status=='UNKNOWN'
        if v is None:return None,not unknown
        y=x^v;q=tuple((r&x).bit_count()-(r&y).bit_count() for r in R)
        assert satisfies(y,P,()) and all(a>=0 and a%2==0 for a in q) and any(q)
        assert y.bit_count()<=x.bit_count()-2
        if history is not None:history.append((k_index,t,x,v,q,B.left))
        x=y;t+=1
    assert all((r&x).bit_count()==1 for r in R)
    return x,True
