"""27-trit S3/C3 *action-sensitive* Heaps observation bridge.

CANONICAL PRIOR OWNERS (not redefined mathematically):
  Base369Ternary27HypervoxelFabricGeometryExact.Ternary27Point
  RecursiveFibreTower.LevelTwoCode (27 ternary endomorphism tables)
  TernaryEndomorphismConjugacyExact (7 functional-graph conjugacy orbits)
  TernaryPermutationS3LawsExact (six permutations)
  ZipfABC6OrderHeapsQuotientExact (ABC six full-Heaps equality)
  PR #1414 polynomial monodromy & rational quaternion u^3=-1/u^6=1
  PR #1407 27*729 Fourier and 3/6/9/27 orbital boundary.

SOURCE THEORY: Cauchy/Frobenius/Burnside orbit counting; Pólya 1937,
S3 finite group action, elementary finite IID occupancy / Heaps curves.
New code Johl Brown-directed / OpenAI ChatGPT, 2026-10-28.
Finite arithmetic ONLY; no spin lift, Abel-Ruffini, physical
monodromy or Ibrahim Monster 3B same-object promotion.
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction
from itertools import permutations, product

TRITS=(-1,0,1)
CUBE=tuple(product(TRITS,repeat=3))
S3=tuple(permutations(range(3)))
C3=((0,1,2),(1,2,0),(2,0,1))


def _word(triple):
    if len(triple)!=3 or any(v not in TRITS or type(v) is not int for v in triple):
        raise ValueError("exact three signed trits required")
    return tuple(triple)


def axis_permute(triple, action):
    """Reorient x/y/z coordinate POSITIONS, not the values."""
    word=_word(triple)
    if tuple(action) not in S3:
        raise ValueError("coordinate action must be a permutation of 3 axes")
    return tuple(word[i] for i in action)


def relabel_values(triple, action):
    """Permute the three VALUES, not x/y/z positions."""
    word=_word(triple)
    if tuple(action) not in S3:
        raise ValueError("value action must be S3")
    return tuple(TRITS[action[TRITS.index(v)]] for v in word)


def conjugate_endomorphism(code, action):
    """Original 27 function-tables action: p composition f composition p^-1.

    This is NOT the axis-only action and NOT the value-only action.
    """
    code=_word(code)
    if tuple(action) not in S3:
        raise ValueError("endomorphism conjugator must be S3")
    inverse=tuple(action.index(i) for i in range(3))
    labels=tuple(TRITS.index(v) for v in code)
    return tuple(TRITS[action[labels[inverse[i]]]] for i in range(3))


def heaps_curve(word):
    seen=set()
    curve=(0,)
    for symbol in _word(word):
        seen.add(symbol)
        curve+=(len(seen),)
    return curve


def orbit_partition(action_set, act):
    """Actual finite orbit sets, not a claim from numerical cardinalities."""
    action_set=tuple(action_set)
    partition={frozenset(act(word,p) for p in action_set) for word in CUBE}
    assert frozenset().union(*partition)==frozenset(CUBE)
    assert sum(len(fibre) for fibre in partition)==27
    return frozenset(partition)


def burnside_fixed_point_counts(action_set, act):
    return tuple(sum(act(x,p)==x for x in CUBE) for p in action_set)


def exact_action_audit():
    actions={
        "coordinate_S3": (S3,axis_permute),
        "coordinate_C3": (C3,axis_permute),
        "value_S3": (S3,relabel_values),
        "endomorphism_conjugacy_S3":(S3,conjugate_endomorphism),
    }
    expected={
        "coordinate_S3":(10,{1:3,3:6,6:1}),
        "coordinate_C3":(11,{1:3,3:8}),
        "value_S3":(5,{3:1,6:4}),
        "endomorphism_conjugacy_S3":(7,{1:1,2:1,3:2,6:3}),
    }
    out={}
    for name,(group,act) in actions.items():
        orbits=orbit_partition(group,act)
        sizes=dict(sorted(Counter(map(len,orbits)).items()))
        fixed=burnside_fixed_point_counts(group,act)
        assert sum(fixed)%len(group)==0
        count=sum(fixed)//len(group)
        assert count==len(orbits)
        assert (count,sizes)==expected[name]
        out[name]={"orbit_count":count,"orbit_size_multiplicity":sizes,
                   "fixed_points":fixed,
                   "heaps_invariant":all(len({heaps_curve(w) for w in orb})==1
                                         for orb in orbits)}
    assert out["value_S3"]["heaps_invariant"]
    assert not out["coordinate_S3"]["heaps_invariant"]
    assert not out["coordinate_C3"]["heaps_invariant"]
    assert not out["endomorphism_conjugacy_S3"]["heaps_invariant"]
    return out


def uniform27_heaps_law():
    """27 typed words interpreted as 3 IID *uniform* type draws.

    This is a specific interpretation and measure. A dialectic cube's
    three semantic axes are NOT intrinsically chronological samples.
    """
    curve_counts=Counter(heaps_curve(word) for word in CUBE)
    expect={
        (0,1,1,1):3,(0,1,1,2):6,
        (0,1,2,2):12,(0,1,2,3):6,
    }
    assert dict(curve_counts)==expect
    law={curve:Fraction(count,27) for curve,count in sorted(curve_counts.items())}
    assert sum(law.values(),Fraction())==1
    # Independent probability for IID Zipf exponent s=0, three ranks:
    # weights (1,1,1) normalize to (1/3,1/3,1/3).
    normalized_zero_exponent_rank_masses=tuple(
        Fraction(1,(rank+1)**0) for rank in range(3))
    z=sum(normalized_zero_exponent_rank_masses,Fraction())
    masses=tuple(w/z for w in normalized_zero_exponent_rank_masses)
    assert masses==(Fraction(1,3),)*3
    independent=Counter()
    for word in product(TRITS,repeat=3):
        weight=Fraction(1)
        for v in word:weight*=masses[TRITS.index(v)]
        independent[heaps_curve(word)]+=weight
    assert law==dict(independent)
    return law


def conditioned_six_order_law():
    """Condition the 27 IID words on all THREE values being distinct.

    Returns the original SSSP six ABC permutations as a *set of label
    words*, not as a second group/carrier; each has conditional mass 1/6.
    This is NOT IID unconditional, nor an equivalence with a nonuniform Zipf.
    """
    distinct=tuple(word for word in CUBE if len(set(word))==3)
    assert len(distinct)==6
    all_words={''.join("ABC"[TRITS.index(x)] for x in word) for word in distinct}
    assert all_words=={"ABC","ACB","BAC","BCA","CAB","CBA"}
    evidence_probability=Fraction(len(distinct),len(CUBE))
    assert evidence_probability==Fraction(2,9)
    law={"".join("ABC"[TRITS.index(x)] for x in word):Fraction(1,6)
         for word in distinct}
    assert sum(law.values(),Fraction())==1
    assert all(heaps_curve(word)==(0,1,2,3) for word in distinct)
    return {"evidence_probability":evidence_probability,"conditional":dict(sorted(law.items()))}


def information_loss_and_nonpromotion():
    """Different action/measurement information losses on the same 27 codes."""
    a=(-1,-1,0)
    b=(-1,0,-1)
    assert axis_permute(a,(0,2,1))==b
    assert heaps_curve(a)!=(heaps_curve(b))
    assert heaps_curve(relabel_values(a,(1,0,2)))==heaps_curve(a)
    # Distinct 5-trit and 3-five-mode cardinalities, from separate PR1414.
    # Cardinalities do not supply a map into the 27-code orbits.
    assert 3**5==243 and 5**3==125 and 243!=125
    assert 3**3==27 and 3**6==729 and 27**2==729
    # Seven functional-graph orbits, five value-label orbits, ten
    # coordinate orbits, and four Heaps curves are NOT interchangeable.
    return {"distinct_ternary_depth5":243,"distinct_five_mode_depth3":125,
            "ternary_cube":27,"double_cube":729,
            "distinct_heaps_curves":len(set(map(heaps_curve,CUBE)))}


def uniform_heaps_curve_multiplicities(alphabet: int, length: int):
    """Count complete novelty curves of length n over a q-symbol alphabet.

    Integer-only pushforward of the EXISTING IID word space; the induced
    probability law is compared against the canonical full_heaps_curve_law
    owner when within its bounded computational budget. No new probability
    carrier or exponent fitting is introduced.

    If s types have appeared, a repeated token has s possible labels;
    a novel type has q-s possible labels. This makes an exact DP over
    the full novelty history, with no need to enumerate q^n whole words.
    """
    from math import comb
    if (type(alphabet) is not int or type(length) is not int
            or not 1<=alphabet<=7 or not 1<=length<=10
            or alphabet**length>30000):
        raise ValueError('bounded positive integer alphabet/length required')
    states={(0,):1}
    for _ in range(length):
        following=Counter()
        for curve,mass in states.items():
            seen=curve[-1]
            if seen:
                following[curve+(seen,)]+=mass*seen
            if seen<alphabet:
                following[curve+(seen+1,)]+=mass*(alphabet-seen)
        states=dict(following)
    assert sum(states.values())==alphabet**length
    expected_profile_count=sum(comb(length-1,j)
        for j in range(min(alphabet-1,length-1)+1))
    assert len(states)==expected_profile_count

    # Reuse the prior full-path PMF owner; do not maintain another
    # IID occupancy model. This bridge only computes integer fibre sizes.
    from zipf_full_heaps_path_distribution_exact import full_heaps_curve_law
    canonical=full_heaps_curve_law((1,)*alphabet,length,'iid')
    expected={curve:Fraction(mass,alphabet**length)
              for curve,mass in states.items()}
    assert expected==canonical
    return dict(sorted(states.items()))


def compare_three_to_five_coding_axes():
    """3^5 vs 5^3: typed orientation changes Heaps complexity.

    11 full-Heaps curves on (3 labels,5 positions) is numerically equal
    to 11 C3-position orbits on (3 labels,3 positions), but NO canonical
    isomorphism or observation-intertwining map is supplied.
    """
    m3n5=uniform_heaps_curve_multiplicities(3,5)
    m5n3=uniform_heaps_curve_multiplicities(5,3)
    assert len(m3n5)==11 and len(m5n3)==4
    assert sum(m3n5.values())==243
    assert sum(m5n3.values())==125
    assert m5n3=={
       (0,1,1,1):5,(0,1,1,2):20,
       (0,1,2,2):40,(0,1,2,3):60}
    assert len(orbit_partition(C3,axis_permute))==len(m3n5)==11
    return {"five_trit_words":243,"their_heaps_curves":11,
            "three_five_mode_words":125,"their_heaps_curves":4,
            "independent_cyclic_cube_orbits":11}


def equality_pattern_heaps_fibres(alphabet: int, length: int):
    """Actual S_q value-relabel quotient and its Heaps observation pushforward.

    Restricted growth patterns canonically encode set partitions (classic
    Stirling/Bell combinatorics), not a new ternary-group carrier.
    For a pattern with k used labels, its orbit of named words has exactly
    (q)_k = q*(q-1)*...*(q-k+1) elements. The original Zipf Heaps fibre
    count is recovered by summing orbit cardinalities over matching curves.
    """
    if (type(alphabet) is not int or type(length) is not int
            or not 1<=alphabet<=7 or not 1<=length<=10
            or alphabet**length>30000):
        raise ValueError('bounded positive alphabet and history length required')

    # Generate restricted-growth strings directly, NOT every named word.
    patterns={(0,)}
    for _ in range(1,length):
        following=set()
        for pattern in patterns:
            top=max(pattern)
            for next_label in range(min(top+1,alphabet-1)+1):
                following.add(pattern+(next_label,))
        patterns=following

    def falling(q,k):
        result=1
        for i in range(k):
            result*=q-i
        return result

    def curve(word):
        known=set();result=[0]
        for label in word:
            known.add(label)
            result.append(len(known))
        return tuple(result)

    by_k=Counter()
    by_curve=Counter()
    pattern_sizes={}
    for pattern in sorted(patterns):
        k=max(pattern)+1
        mass=falling(alphabet,k)
        pattern_sizes[pattern]=mass
        by_k[k]+=1
        by_curve[curve(pattern)]+=mass

    assert sum(pattern_sizes.values())==alphabet**length
    # Existing canonical uniform Heaps fibres and conditional IID path
    # interpretation are independently checked by its original owner.
    expected=uniform_heaps_curve_multiplicities(alphabet,length)
    assert dict(by_curve)==expected

    return {
        'pattern_count':len(patterns),
        'stirling_counts':dict(sorted(by_k.items())),
        'pattern_orbit_cardinalities':pattern_sizes,
        'heaps_curve_count':len(by_curve),
        'heaps_curve_fibres':dict(sorted(by_curve.items())),
    }


def exact_three_five_pattern_boundary():
    """Structural calculation behind 3^5 versus 5^3, not an object weld."""
    triad_depth5=equality_pattern_heaps_fibres(3,5)
    five_mode_depth3=equality_pattern_heaps_fibres(5,3)
    triad_depth3=equality_pattern_heaps_fibres(3,3)
    assert triad_depth5['stirling_counts']=={1:1,2:15,3:25}
    assert triad_depth5['pattern_count']==41
    assert triad_depth5['heaps_curve_count']==11
    assert five_mode_depth3['stirling_counts']=={1:1,2:3,3:1}
    assert five_mode_depth3['pattern_count']==5
    assert five_mode_depth3['heaps_curve_count']==4
    assert triad_depth3['pattern_count']==5
    assert triad_depth3['heaps_curve_count']==4
    assert len(orbit_partition(C3,axis_permute))==11
    # Equal number of 3^5 Heaps curves and 3^3 C3 coordinate orbits
    # is NOT equality of set partitions, orbit actions or their measures.
    return {'three_raised_five':triad_depth5,
            'five_raised_three':five_mode_depth3,
            'three_cubed':triad_depth3}
