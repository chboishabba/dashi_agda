"""Two-orbit transversal diagnostics attached to actual reachable epoch events.
Support counts never become extra paid time events.
"""
from itertools import product
from check_pnp_recursive_quotient import act, orbit_epoch, minimal_hits, orbit_supports
from check_pnp_live_signed_orbit_join import Budget, Refused, source_group

def transported(x,g):
    return tuple(v for _,v in sorted(act(g,dict(enumerate(x))).items()))

def two_orbit_supports(x,y,G,B):
    B.pay(len(G)*(1+len(x)+len(y)))
    X={transported(x,g) for g in G};Y={transported(y,g) for g in G}
    B.pay(len(X)*len(Y)*(1+len(x)))
    return frozenset(frozenset(i for i,(v,w) in enumerate(zip(a,b)) if v!=w)
                     for a in X for b in Y)

def actual_epoch_family(x,domain,G,state,consumer,observe,cuts,cap):
    """Complete disjoint-window receipt or refusal, with original event IDs.
    Only the actual original rival is assumed reachable in its epoch;
    transformed representatives are support diagnostics, not new runs.
    """
    B=Budget(cap);receipts=[];paid=set()
    if any(a>=b for a,b in zip(cuts,cuts[1:])):raise ValueError("cuts")
    try:
        for a,b in zip(cuts,cuts[1:]):
            q=orbit_epoch(x,domain,G,state,consumer,observe,a,b,B)
            if q is None:continue
            S=two_orbit_supports(x,q["rival"],G,B)
            assert frozenset() not in S
            H=minimal_hits(S,len(x),B)
            j=q["event"]
            assert a<=j<b and j not in paid
            paid.add(j);receipts.append(dict(q,window=(a,b),two_supports=S,two_hits=H))
        assert len(paid)<=cuts[-1]-cuts[0] if cuts else not paid
        return dict(events=tuple(receipts),paid=len(paid),used=B.used)
    except Refused:return None

def main():
    x=(1,0,0);y=(1,1,0)
    G=source_group((),3,(),(),((1,2,0),(0,2,1)),Budget(10000))
    B=Budget(100000)
    a=minimal_hits(orbit_supports(x,y,G,B),3,B)
    b=minimal_hits(two_orbit_supports(x,y,G,B),3,B)
    assert a==(frozenset((1,2)),) and b==(frozenset(range(3)),)
    D=tuple(product((0,1),repeat=3));f=lambda z:sum(z)
    # Repeated externally-observed toy epochs; no SAT lower bound.
    state=lambda z,t:0 if t%2==0 else f(z)
    observe=lambda z,t:state(z,t+1)
    q=actual_epoch_family(x,D,G,state,f,observe,(0,1,2,3),1000000)
    assert q["paid"]==2 and tuple(z["event"] for z in q["events"])==(0,2)
    assert actual_epoch_family(x,D,G,state,f,observe,(0,1),0) is None
    print(dict(two_orbit_stronger=1,actual_event_ids=2,refusal=1))
if __name__=="__main__":main()
