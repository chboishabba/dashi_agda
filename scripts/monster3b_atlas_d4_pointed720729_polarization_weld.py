#!/usr/bin/env python3
"""Actual ATLAS 2.Suz:2 D4: stable Schr polarization and 720-corner obstruction.

Reuses the ORIGINAL AtlasRep matrix bytes, exact source-word helper and
nondegenerate alternating form from this PR; no duplicated source generators.
Original mathematics: ATLAS/AtlasRep; Wilson 1988; Barraclough--Wilson 2007;
finite symplectic/Heisenberg representation theory (Serre, Terras).
This is exact F3 arithmetic and a source D4 quotient result, NOT a
selected Monster class fusion, 6.Suz-78 occurrence or action inside W_zeta.
"""
import json
from itertools import product
from pathlib import Path
import monster3b_atlas_actual_d4_word_witness as Atlas

def mul(A,B):
    cols=list(zip(*B))
    return [[sum(a*b for a,b in zip(row,col))%3 for col in cols] for row in A]

def transpose(A):return [list(row) for row in zip(*A)]
def diff(A,B):return [[(x-y)%3 for x,y in zip(u,v)] for u,v in zip(A,B)]
def rank(A):return Atlas.rectangular_rank_mod3(A)

def nullspace(A):
    R=[[x%3 for x in row] for row in A]
    height,width=len(R),len(R[0])
    pivots=[];k=0
    for j in range(width):
        i=next((l for l in range(k,height) if R[l][j]),None)
        if i is None:continue
        R[i],R[k]=R[k],R[i]
        inv=1 if R[k][j]==1 else 2
        R[k]=[(inv*x)%3 for x in R[k]]
        for l in range(height):
            if l!=k:
                factor=R[l][j]
                R[l]=[(x-factor*y)%3 for x,y in zip(R[l],R[k])]
        pivots.append(j);k+=1
        if k==height:break
    result=[]
    for j in range(width):
        if j in pivots:continue
        v=[0]*width;v[j]=1
        for t,p in enumerate(pivots):v[p]=(-R[t][j])%3
        result.append(v)
    return transpose(result)

def determinant(A):
    R=[[v%3 for v in row] for row in A];d=1
    for j in range(len(R)):
        i=next((i for i in range(j,len(R)) if R[i][j]),None)
        if i is None:return 0
        if i!=j:R[i],R[j]=R[j],R[i];d=-d%3
        u=R[j][j];d=d*u%3
        for k in range(j+1,len(R)):
            f=R[k][j]*u%3
            R[k]=[(x-f*y)%3 for x,y in zip(R[k],R[j])]
    return d

def audit(root):
    data=root/'data'/'atlas'
    for filename,sha in Atlas.SOURCE_DIGESTS.items():
        import hashlib
        if hashlib.sha256((data/filename).read_bytes()).hexdigest()!=sha:
            raise ValueError('original ATLAS source hash mismatch: '+filename)
    C=Atlas.parse_meataxe(data/'2Suzd2G1-f3r12aB0.m1')
    D=Atlas.parse_meataxe(data/'2Suzd2G1-f3r12aB0.m2')
    J=Atlas.form()
    W=Atlas.evaluate(Atlas.W_ORDER10,C,D)
    m=Atlas.power(W,5)
    g=Atlas.evaluate(Atlas.CONJUGATOR,C,D)
    gi=Atlas.evaluate(Atlas.inverse_word(Atlas.CONJUGATOR),C,D)
    r=Atlas.mm(m,Atlas.mm(Atlas.mm(g,m),gi))
    I=Atlas.ident();NI=Atlas.neg(I)
    assert Atlas.mm(m,m)==I and Atlas.mm(r,r)==NI
    assert Atlas.mm(m,Atlas.mm(r,m))==Atlas.power(r,3)
    assert mul(transpose(m),mul(J,m))==Atlas.neg(J)
    assert mul(transpose(r),mul(J,r))==J
    U=nullspace(diff(m,I))
    assert len(U)==12 and len(U[0])==6 and rank(U)==6
    assert rank(J)==12
    assert not any(x for row in mul(transpose(U),mul(J,U)) for x in row)
    Q=mul(transpose(U),mul(J,mul(r,U)))
    assert Q==transpose(Q) and rank(Q)==6
    det=determinant(Q)
    assert det==2  # split Witt index 3, so there exists a totally singular 3-space
    def apply(A,v):return [sum(a*b for a,b in zip(row,v))%3 for row in A]
    def q(v,w):return sum(x*y for x,y in zip(v,apply(Q,w)))%3
    chosen=[]
    for v in product(range(3),repeat=6):
        if not any(v) or q(v,v):continue
        if any(q(v,w) for w in chosen):continue
        if rank(transpose(chosen+[v]))!=len(chosen)+1:continue
        chosen.append(v)
        if len(chosen)==3:break
    assert len(chosen)==3
    vectors=[apply(U,v) for v in chosen]
    columns=[v for x in vectors for v in (x,apply(r,x))]
    L=transpose(columns);E2=transpose(columns[:2])
    assert rank(L)==6 and rank(E2)==2
    assert not any(x for row in mul(transpose(L),mul(J,L)) for x in row)
    for action in (m,r):
        assert rank([u+v for u,v in zip(L,mul(action,L))])==6
        assert rank([u+v for u,v in zip(E2,mul(action,E2))])==2
    # L = three D4-stable 2D blocks, each with
    # r(a,b)=(-b,a), m(a,b)=(a,-b). The quotient by E2 is E + E.
    def applyword(word,x):
        for t in word:
            pairs=list(zip(x[::2],x[1::2]))
            x=tuple(z%3 for a,b in pairs for z in ((-b,a) if t=='r' else (a,-b)))
        return x
    words=('', 'r','rr','rrr','m','mr','mrr','mrrr')
    quotient=list(product(range(3),repeat=4))
    assert len(quotient)==81
    fixed={w:sum(applyword(w,x)==x for x in quotient) for w in words}
    assert sorted(fixed.values())==[1,1,1,9,9,9,9,81]
    nonzero=[x for x in quotient if any(x)]
    fixed80={w:sum(applyword(w,x)==x for x in nonzero) for w in words}
    assert sorted(fixed80.values())==[0,0,0,8,8,8,8,80]
    rem=set(nonzero);orbits=[]
    while rem:
        x=min(rem)
        orbit={applyword(w,x) for w in words}
        assert orbit<=rem
        rem-=orbit;orbits.append(orbit)
    histogram={str(k):sum(len(o)==k for o in orbits) for k in (1,2,4,8)}
    assert histogram=={'1':0,'2':0,'4':8,'8':6}
    assert len(orbits)==14
    # If E+E nonzero 80-set = (a D4 eight-corner set) x (TRIVIAL Fin10),
    # every D4 fixed count is divisible by ten; actual reflections fix 8.
    assert fixed80['m']==8 and fixed80['m']%10!=0
    # Stronger test against the PRE-EXISTING literal cube-corner chart:
    # Natural planar square D4 on OuterSign^3 has
    #     r(x,y,z)=(-y,x,z), m(x,y,z)=(x,-y,z).
    # Its axis-mirror has ZERO fixed corners, while the ACTUAL SOURCE
    # quotient has EIGHT fixed labels for EVERY reflection. Any D4-map
    # quotient80 -> corners8 would send each source mirror-fixed label
    # to a target mirror-fixed corner: impossible. This excludes ALL
    # ten-sheet systems retaining an equivariant geometric-corner
    # projection, including twisted fibre actions, not just trivial10.
    corners=list(product((-1,1),repeat=3))
    def corner_action(w,p):
        for ch in w:
            p=(-p[1],p[0],p[2]) if ch=='r' else (p[0],-p[1],p[2])
        return p
    corner_fixed={w:sum(corner_action(w,x)==x for x in corners) for w in words}
    assert corner_fixed['m']==0 and corner_fixed['mr']==4
    assert fixed80['m']==8 and fixed80['mr']==8
    assert sorted(corner_fixed.values())==[0,0,0,0,0,4,4,8]
    # NEW POSITIVE CONTRAST: the natural cube corners are IMPOSSIBLE, but
    # a DIFFERENT eight-label D4 quotient DOES exist. Reuse literal source
    # ATLAS D4 words and E+E coordinate chart above; no new generators.
    # Its target is an axis-reflection 4-orbit DISJOINT union a diagonal
    # reflection 4-orbit. Assign 3 free 8-orbits to each half, so all
    # eight target fibres have exactly ten nonzero quotient vectors.
    from collections import Counter, defaultdict
    types=defaultdict(list)
    for orb in orbits:
        rep=min(orb)
        stabilizer=[w for w in words if applyword(w,rep)==rep]
        if len(orb)==4:
            assert len(stabilizer)==2
            invol=[w for w in stabilizer if w][0]
            assert invol in ('m','mr','mrr','mrrr')
            typ='axis' if len(invol)-1 in (0,2) else 'diagonal'
        else:
            assert len(orb)==8 and stabilizer==['']
            typ='free'
        types[typ].append((rep,orb,stabilizer))
    assert {name:len(rows) for name,rows in types.items()}=={
        'axis':4,'diagonal':4,'free':6}
    target={'axis':set(types['axis'][0][1]),
            'diagonal':set(types['diagonal'][0][1])}
    quotient_map={}
    bundles=([(row,'axis') for row in types['axis']]
          + [(row,'diagonal') for row in types['diagonal']]
          + [(row,'axis' if i<3 else 'diagonal')
             for i,row in enumerate(types['free'])])
    for (rep,orb,stab),kind in bundles:
        cand=[v for v in target[kind]
              if all(applyword(w,v)==v for w in stab)]
        assert cand
        y=min(cand)
        for w in words:
            x=applyword(w,rep)
            value=(kind,applyword(w,y))
            if x in quotient_map:assert quotient_map[x]==value
            quotient_map[x]=value
    assert len(quotient_map)==80
    assert set(Counter(quotient_map.values()).values())=={10}
    for x in nonzero:
        for w in words:
            kind,y=quotient_map[x]
            assert quotient_map[applyword(w,x)]==(kind,applyword(w,y))
    # The ten-sheet action is NONTRIVIAL: this quotient80 has 6 free
    # 8-orbits, while 10 copies of the target mixed8 contain ONLY
    # 4-orbits. This is a positive twisted-sheet construction,
    # NOT a resurrection of the natural cube-corner quotient.
    mixed_fixed={w:sum(applyword(w,t)==t for kind,orb in target.items()
                       for t in orb) for w in words}
    assert mixed_fixed['m']==2 and mixed_fixed['mr']==2
    mirror_fibre_fixed={}
    for w in ('m','mr'):
        sites=[(kind,y) for kind,T in target.items() for y in T
               if applyword(w,y)==y]
        assert len(sites)==2
        counts=[sum(applyword(w,x)==x for x in nonzero
                    if quotient_map[x]==site) for site in sites]
        assert counts==[4,4]
        mirror_fibre_fixed[w]=counts
    return dict(status='PASS_original_ATLAS_D4_invariant_polarization_and_corner10_nogo',
        original_ATLAS_sha256_verified=True,
        source_D4_word_relations_verified=True,
        six_dim_mirror_plus_lagrangian=True,
        source_rank6_symmetric_form_det_mod3=det,
        source_rank6_Witt_index=3,
        chosen_isotropic_three_vectors=[list(v) for v in chosen],
        source_D4_stable_6D_Lagrangian_columns=columns,
        source_D4_stable_2D_plane_columns=columns[:2],
        source_D4_9point_support_stable_at_label_level=True,
        quotient_F3four_size=81,nonzero_quotient_size=80,
        source_D4_nonzero_fixed_counts=fixed80,
        source_D4_nonzero_orbit_sizes=histogram,
        source_D4_orbit_count=len(orbits),
        D4_equivariant_10_copies_of_one_corner8_set_possible=False,
        natural_cube_corner8_fixed_counts=corner_fixed,
        D4_equivariant_projection_to_natural_cube_corner8_possible=False,
        mixed_D4_eight_target_exists=True,
        mixed_D4_target_orbit_types={'axis4':1,'diagonal4':1},
        mixed_D4_quotient80_each_target_fibre_size=10,
        mixed_D4_quotient80_equivariant=True,
        mixed_D4_target_fixed_counts=mixed_fixed,
        mixed_D4_reflection_fixed_source_points_per_target_fibre=mirror_fibre_fixed,
        ten_sheet_D4_action_necessarily_twisted=True,
        natural_cube_corner_no_go_still_valid=True,
        nontrivial_D4_mixing_of_ten_sheets_excluded=False,
        actual_Monster_N3B_D4_class_fusion_proved=False,
        literal_Monster_source_character_78_selected=False,
        action_inside_single_zeta_phase_constructed=False,
        Agda_kernel_checked=False)
if __name__=='__main__':
    print(json.dumps(audit(Path(__file__).resolve().parents[1]),indent=2))
