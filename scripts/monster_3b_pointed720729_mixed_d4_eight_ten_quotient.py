#!/usr/bin/env python3
"""Exact 720=8*10*9 D4 quotient with TWISTED ten-sheets; 729=720+9.

Uses existing #1098 source-theoretic fact: selected ATLAS 2.Suz:2 D4
acts on the 4D affine quotient as E ⊕ E over F3, after a D4-stable
9-point plane. D4 has order8, coprime to3, so module splitting exists
(Maschke); the present E^3 chart is a CHOSEN isomorphic abstract model,
not a literal Atlas generator-coordinate equivalence or Monster action.

The natural geometric cube-corner8 quotient is impossible (#1098/#1250);
the different MIXED-ORBIT eight-site D4 target constructed here has one
axis-reflection 4-orbit and one diagonal-reflection 4-orbit, with exactly
10 points over every site. The sheet D4 action is transported and twisted;
it is NOT D4 acting trivially on a Fin10 independent factor.

Original mathematics: Maschke, ordinary finite D4 G-set orbit theory.
Source ATLAS generators/polarization: existing #1098 owner.
Earlier 720+9 addresses: Base369PointedAppraisalFibreExact, not
independent Monster characters/Mathieu ordered-two-point stabilizers.
"""
from collections import Counter, defaultdict
from itertools import product
from math import comb
import json

F=range(3)
G=tuple(product(range(2),range(4)))
Q=tuple(product(F,repeat=4))
INNER=tuple(product(F,repeat=2))
ZERO=(0,0,0,0)

def rotate(v):
    if len(v)%2:raise ValueError("only a direct sum of D4 standard E")
    out=[]
    for a,b in zip(v[::2],v[1::2]):out.extend(((-b)%3,a))
    return tuple(out)

def mirror(v):
    return tuple(x if i%2==0 else (-x)%3 for i,x in enumerate(v))

def act(g,v):
    eps,k=g
    if eps:v=mirror(v)
    for _ in range(k):v=rotate(v)
    return v

def orbit(v):
    return tuple(sorted({act(g,v) for g in G}))

def stabilizer(v):
    return tuple(g for g in G if act(g,v)==v)

def build():
    seen=set();classes=defaultdict(list)
    for v in Q:
        if v==ZERO or v in seen:continue
        orb=orbit(v);seen.update(orb)
        rep=orb[0];stab=stabilizer(rep)
        kind=(len(orb),tuple(g[1]%2 for g in stab if g[0]))
        classes[kind].append((rep,orb,stab))
    AXIS=(4,(0,));DIAG=(4,(1,));FREE=(8,())
    assert set(classes)=={AXIS,DIAG,FREE}
    assert [len(classes[x]) for x in (AXIS,DIAG,FREE)]==[4,4,6]
    targets={k:classes[k][0][1] for k in (AXIS,DIAG)}
    all_targets=tuple(sorted((k,p) for k,T in targets.items() for p in T))
    assert len(all_targets)==8

    # ALL balanced D4-equivariant quotient maps, not merely one witness.
    # An equivariant map of a transitive orbit G/H is determined by a
    # target point FIXED by H. Exact stabilizer counts give:
    # axis4 -> axis4:2, diag4 -> diag4:2,
    # free8 -> either target four-orbit:4 choices each.
    # Every target site must have 10 preimages. The four fixed-kind
    # 4-orbits contribute 4 per site; each free8 orbit assigned to that
    # kind contributes 2 more. Hence precisely 3 free8 to each kind.
    hom_options=Counter()
    for kind in (AXIS,DIAG,FREE):
        by_target=Counter()
        for rep,orb,stab in classes[kind]:
            choices={target:sum(all(act(g,y)==y for g in stab)
                                for y in targets[target])
                     for target in (AXIS,DIAG)}
            assert choices==(
                {AXIS:2,DIAG:0} if kind==AXIS else
                {AXIS:0,DIAG:2} if kind==DIAG else
                {AXIS:4,DIAG:4})
            by_target[tuple(sorted(choices.items()))]+=1
        assert sum(by_target.values())==len(classes[kind])
        hom_options[kind]=dict(by_target)
    # Independent dynamic polynomial enumeration: for every source
    # orbit multiply by the exact number of maps into each target type.
    # The two indices count FREE8 source orbits assigned to axis/diag.
    count={(0,0):1}
    for kind in (AXIS,DIAG,FREE):
        for rep,orb,stab in classes[kind]:
            options={t:sum(all(act(g,y)==y for g in stab)
                           for y in targets[t])
                     for t in (AXIS,DIAG)}
            nxt=defaultdict(int)
            for (a,b),v in count.items():
                for t,choices in options.items():
                    if choices:
                        nxt[(a+(kind==FREE and t==AXIS),
                             b+(kind==FREE and t==DIAG))]+=v*choices
            count=dict(nxt)
    all_equivariant_maps=sum(count.values())
    balanced_maps=count[(3,3)]
    independent_formula=comb(6,3)*(2**8)*(4**6)
    assert balanced_maps==independent_formula==20971520
    assert all_equivariant_maps==(2**8)*(8**6)==67108864
    # Equivariant automorphisms of the target are two per reflection
    # orbit, hence four overall. Their action on SURJECTIONS is free.
    target_auts=2*2
    assert balanced_maps%target_auts==0
    balanced_mod_target_relabelling=balanced_maps//target_auts
    assert balanced_mod_target_relabelling==5242880

    source_orbits=([(row,AXIS) for row in classes[AXIS]]+
                   [(row,DIAG) for row in classes[DIAG]]+
                   [(row,AXIS if i<3 else DIAG)
                    for i,row in enumerate(classes[FREE])])
    quotient={}
    for (rep,orb,stab),kind in source_orbits:
        possible=[y for y in targets[kind] if all(act(g,y)==y for g in stab)]
        assert possible,"source stabilizer must be contained in target stabilizer"
        selected=min(possible)
        for g in G:
            x=act(g,rep);y=act(g,selected)
            if x in quotient:assert quotient[x]==(kind,y)
            quotient[x]=(kind,y)
    assert len(quotient)==80
    assert set(quotient.values())==set(all_targets)
    assert set(Counter(quotient.values()).values())=={10}
    for x in quotient:
        for g in G:
            kind,y=quotient[x]
            assert quotient[act(g,x)]==(kind,act(g,y))
    fibres={site:tuple(sorted(x for x in quotient if quotient[x]==site))
            for site in all_targets}
    index={x:(site,fibres[site].index(x)) for x,site in quotient.items()}
    assert len(index)==80
    # FULL 729 address codec as (site8,sheet10,inner9) plus centre inner9.
    encoded={}
    for q in Q:
        for t in INNER:
            address=("central",t) if q==ZERO else (
                "outer",all_targets.index(index[q][0]),index[q][1],t)
            assert address not in encoded
            encoded[address]=(q,t)
    assert len(encoded)==729
    assert len([a for a in encoded if a[0]=="outer"])==720
    assert len([a for a in encoded if a[0]=="central"])==9
    inverse={(q,t):a for a,(q,t) in encoded.items()}
    assert len(inverse)==729
    def transported(g,a):
        q,t=encoded[a]
        return inverse[(act(g,q),act(g,t))]
    for a in encoded:
        for g in G:
            b=transported(g,a)
            assert b in encoded and b[0]==a[0]
    # Twisting is forced in the SOURCE QUOTIENT80: it has six free
    # size8 D4 orbits, while Mixed8 x Fin10 with trivial sheet action
    # would have only size4 quotient orbits. It is NOT enough merely
    # to cite size8 orbits after tensoring with INNER9: even a trivial
    # sheet can acquire size8 product orbits through distinct stabilizers
    # in Mixed8 and the nontrivial INNER9 D4 action.
    outer_orbits=Counter()
    visited=set()
    for a in encoded:
        if a[0]!="outer" or a in visited:continue
        ob={transported(g,a) for g in G}
        visited|=ob
        outer_orbits[len(ob)]+=1
    assert outer_orbits==Counter({8:78,4:24})
    assert sum(k*v for k,v in outer_orbits.items())==720
    fixchar={}
    for name,g in (("identity",(0,0)),("half_turn",(0,2)),
                   ("quarter_turn",(0,1)),("axis_mirror",(1,0)),
                   ("diagonal_mirror",(1,1))):
        full=sum(transported(g,a)==a for a in encoded)
        outer=sum(transported(g,a)==a for a in encoded if a[0]=="outer")
        centre=full-outer
        fixchar[name]={"all729":full,"outer720":outer,"centre9":centre}
    assert [fixchar[k]["all729"] for k in fixchar]==[729,1,1,27,27]
    assert [fixchar[k]["outer720"] for k in fixchar]==[720,0,0,24,24]
    assert [fixchar[k]["centre9"] for k in fixchar]==[9,1,1,3,3]
    # Integer D4 representation ring certificate, class sizes 1,1,2,2,2.
    # This is the representation of the CHOSEN D4 geometric G-set,
    # not a claim about the actual 6.Suz/Monster 90 multiplicity factor.
    irr={"A1":(1,1,1,1,1),"A2":(1,1,1,-1,-1),
         "B1":(1,1,-1,1,-1),"B2":(1,1,-1,-1,1),
         "E":(2,-2,0,0,0)}
    def decompose(key):
        char=[fixchar[z][key] for z in fixchar]
        terms={}
        for name,values in irr.items():
            dividend=sum(w*x*y for w,x,y in
                         zip((1,1,2,2,2),char,values))
            assert dividend%8==0
            terms[name]=dividend//8
            assert terms[name]>=0
        return terms
    irrep_720=decompose("outer720")
    irrep_9=decompose("centre9")
    irrep_729=decompose("all729")
    assert irrep_720==dict(A1=102,A2=78,B1=90,B2=90,E=180)
    assert irrep_9==dict(A1=3,A2=0,B1=1,B2=1,E=2)
    assert irrep_729==dict(A1=105,A2=78,B1=91,B2=91,E=182)
    assert sum(act((1,0),site[1])==site[1] for site in all_targets)==2
    assert sum(act((1,1),site[1])==site[1] for site in all_targets)==2
    reflection_fibre_fixed={}
    for name,g in (("axis",(1,0)),("diagonal",(1,1))):
        sites=[site for site in all_targets if act(g,site[1])==site[1]]
        values=[sum(act(g,x)==x for x in fibres[site]) for site in sites]
        assert len(sites)==2 and values==[4,4]
        reflection_fibre_fixed[name]=values

    # Existing natural cube-corner8 axis reflection has ZERO fixed points.
    return dict(status="PASS_exact_noncanonical_mixed_D4_eight_by_ten_by_nine",
        quotient80_source_orbits={"axis_four":4,"diagonal_four":4,"free_eight":6},
        mixed_eight_target_orbits={"axis_four":1,"diagonal_four":1},
        per_target_fibre_cardinalities=sorted(Counter(quotient.values()).values()),
        exact_balanced_equivariant_quotient_count=balanced_maps,
        all_equivariant_quotient_count=all_equivariant_maps,
        balanced_count_independent_stabilizer_formula=independent_formula,
        equivariant_target_automorphism_count=target_auts,
        balanced_mod_target_automorphisms=balanced_mod_target_relabelling,
        not_canonical_from_D4_and_uniform_fibres_alone=True,
        lifted_outer_cardinality=720,central_cardinality=9,total=729,
        source_axis_reflection_fixed_nonzero80=8,
        mixed_target_axis_reflection_fixed8=2,
        natural_cube_corners_axis_reflection_fixed8=0,
        classwise_characters=fixchar,
        outer_orbit_sizes=dict(outer_orbits),
        irrep_720=irrep_720,irrep_9=irrep_9,irrep_729=irrep_729,
        mirror_fixed_points_inside_two_fixed_target_fibres=reflection_fibre_fixed,
        nontrivial_ten_sheet_D4_twisting_required=True,
        old_natural_cube_corner_quotient_resurrected=False,
        full_Heisenberg_equivariance_proved=False,
        source_Atlas_coordinate_intertwiner_proved=False,
        actual_Monster_normalizer_intertwiner_proved=False)

if __name__=="__main__":
    print(json.dumps(build(),indent=2))
