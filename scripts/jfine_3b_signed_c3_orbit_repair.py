#!/usr/bin/env python3
"""Construct D4 signed orbit local systems and lift over C3.

ORIGINAL SOURCES: Barraclough--Wilson (2007), ATLAS Monster class fusion,
Breuer/CTblLib; prior E/phase action and proof roles live in existing
Monster3BPhaseTransportExact, Monster3BCentralCharacterInertiaExact.
PR #1148 supplies the CHANGED eight-trit GSp D4 quotient model:
A1+A2+2B1+2B2+E; it is not the geometric 3x3 D4.
This producer constructs a new signed MONOMIAL D4 representation on the
unchanged pointed basis and checks C3 covariance. It deliberately does NOT
claim full H4 covariance, a Monster subgroup, or 6.Suz character selection.
"""
import itertools
import json

F3=3
G=tuple((k,e) for e in (0,1) for k in range(4))
R=(1,0)
M=(0,1)
def mul(g,h):
    k,e=g;l,f=h
    return ( (k+(l if not e else -l))%4, e^f )
def inv(g):
    k,e=g
    return ((-k)%4,0) if not e else g
def dot(a,b):return sum(x*y for x,y in zip(a,b))%3
def ab(v):
    te,tc,be,bc,xe,ye,xc,yc=v
    return (tc,bc,yc,ye),(te,be,xc,xe)
def rotation(x):
    j,v,c=x
    te,tc,be,bc,xe,ye,xc,yc=v
    w=(te,tc,-be%3,-bc%3,-ye%3,xe,-xc%3,-yc%3)
    a,b=ab(v);aa,bb=ab(w)
    cc=(c+dot(a,b)-dot(aa,bb))%3
    jj=j if j<2 else 2+(j-2+1)%4 if j<6 else 6+(j-6+1)%4
    return jj,w,cc
def reflection(x):
    j,v,c=x
    te,tc,be,bc,xe,ye,xc,yc=v
    w=(te,-tc%3,be,-bc%3,xe,-ye%3,xc,-yc%3)
    a,b=ab(v);aa,bb=ab(w)
    cc=(-c-dot(a,b)-dot(aa,bb))%3
    jj=j if j<2 else 2+(-(j-2))%4 if j<6 else 6+(1-(j-6))%4
    return jj,w,cc
def act(g,x):
    k,e=g
    if e:x=reflection(x)
    for _ in range(k):x=rotation(x)
    return x
def qact(g,q):return act(g,(q[0],q[1],0))[:2]
def orbit(q):return {qact(g,q) for g in G}
def selected():
    reps={'fixed':[],'axis':[],'diagonal':[]};seen=set()
    for v in itertools.product(range(3),repeat=8):
        q=(0,v)
        if q in seen:continue
        pts=orbit(q);seen.update(pts)
        H=[g for g in G if qact(g,q)==q]
        kind=('fixed' if len(H)==8 else
            'axis' if len(H)==2 and H[1][1] and H[1][0]%2==0 else
            'diagonal' if len(H)==2 and H[1][1] and H[1][0]%2 else '')
        if kind and len(reps[kind])<(1 if kind=='fixed' else 9):
            reps[kind].append(q)
        if [len(reps[k]) for k in ('fixed','axis','diagonal')]==[1,9,9]:
            return reps
    raise AssertionError("18 reflection-stabilized quotient orbits missing")
def local_system(q):
    pts=orbit(q)
    representatives={}
    for g in G:
        y=qact(g,q)
        if y not in representatives:representatives[y]=g
    H={g for g in G if qact(g,q)==q}
    def sign(g,y):
        h=mul(mul(inv(representatives[qact(g,y)]),g),representatives[y])
        assert h in H
        return -1 if h[1] else 1
    for y in pts:
        for g,h in itertools.product(G,G):
            assert sign(mul(g,h),y)==sign(g,qact(h,y))*sign(h,y)
    return pts,sign
def central_plus(x):return x[0],x[1],(x[2]+1)%3
def central_minus(x):return x[0],x[1],(x[2]-1)%3

def audit():
    reps=selected()
    systems=[(kind,q,*local_system(q)) for kind in reps for q in reps[kind]]
    signs={y:sign for _,_,pts,sign in systems for y in pts}
    assert len(signs)==73
    def weight(g,x):
        q=x[:2]
        return signs[q](g,q) if q in signs else 1
    checks=0
    for q in signs:
        for c in range(3):
            x=(q[0],q[1],c)
            for g in G:
                gx=act(g,x)
                assert weight(g,central_plus(x))==weight(g,x)
                assert weight(g,central_minus(x))==weight(g,x)
                assert act(g,central_plus(x))==(central_minus(gx) if g[1] else central_plus(gx))
                for h in G:
                    assert weight(mul(g,h),x)==weight(g,act(h,x))*weight(h,x)
                    checks+=1
    assert checks==73*3*8*8==14016
    keys=('one','half','quarter','axis','diagonal')
    reps_g={'one':(0,0),'half':(2,0),'quarter':(1,0),
            'axis':(0,1),'diagonal':(1,1)}
    delta={name:sum(s(g,y)-1 for _,_,pts,s in systems for y in pts if qact(g,y)==y)
           for name,g in reps_g.items()}
    assert delta=={'one':0,'half':0,'quarter':0,'axis':-38,'diagonal':-38}
    base=(196830,4374,54,324,324)
    monster=(196883,4371,51,275,275)
    repaired=tuple(v+delta[k] for k,v in zip(keys,base))
    residual=tuple(w-v for w,v in zip(monster,repaired))
    assert residual==(53,-3,-3,-11,-11)
    # Full D4 character decomposition, not just integer dimensionality.
    irreps={'A1':(1,1,1,1,1),'A2':(1,1,1,-1,-1),
            'B1':(1,1,-1,1,-1),'B2':(1,1,-1,-1,1),
            'E':(2,-2,0,0,0)}
    inner={name:sum(a*b*w for a,b,w in zip(residual,chi,(1,1,2,2,2)))//8
           for name,chi in irreps.items()}
    assert inner=={'A1':0,'A2':11,'B1':7,'B2':7,'E':14}
    # A unit element and a generic regular H4 translate with SAME marker
    # have different signed mirror coefficients; this violates the
    # needed source H4-semilinear covariance.
    q0=(0,(0,)*8)
    assert q0 in signs and weight(M,(0,(0,)*8,0))==-1
    witness=next((q for q in itertools.product(range(3),repeat=8)
        if (0,q) not in signs),None)
    assert witness is not None
    assert weight(M,(0,witness,0))==1
    return {
      'schema':'jfine-D4-signed-C3-compatible-model-v1',
      'selected_orbits':{k:len(v) for k,v in reps.items()},
      'signed_quotient_basis_labels':73,
      'signed_full_c3_basis_labels':219,
      'D4_and_C3_checks':checks,
      'trace_corrections':delta,
      'repaired_bulk_character':dict(zip(keys,repaired)),
      'residual_character':dict(zip(keys,residual)),
      'residual_irreducible_multiplicities':inner,
      'all_residual_multiplicities_nonnegative':True,
      'centre_C3_conjugacy_verified':True,
      'preserves_source_regular_H4_action':False,
      'regular_H4_incompatibility_witness':True,
      'actual_Monster_normalizer_constructed':False,
      'Agda_or_GAP_kernel_receipt':False
    }
if __name__=='__main__':print(json.dumps(audit(),indent=2,sort_keys=True))
