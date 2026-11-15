#!/usr/bin/env python3
"""Full finite S3 extension of marked-sheet C3 with coarse punctured-27 pair.

Fine: reflect ONLY selected trit 0 -> 0, 1 <-> 2, reversing C3.
Coarse: 54 = 1 invariant + (1 seam + two 26-state oriented punctured
ternary cubes). C2 swaps the two 26-state copies, fixes invariant/seam;
C3 fixes all 54 coarse basis states. D4 acts on the source cube's x-y
plane, preserving z and the excluded origin, and permutes marker/sheet
together on fine coordinates. No Griess/FLM 3B action asserted.

Exhaustive exact-integer checks of 196884 states and three S3 character
multiplicities, with no dense 196884^2 matrix.
"""
import json
try:
    from scripts import check_monster196884_native_c3_d4_intertwiner as C
except ImportError:
    import check_monster196884_native_c3_d4_intertwiner as C

PUNCTURED=tuple((x,y,z) for z in (-1,0,1) for y in (-1,0,1)
                for x in (-1,0,1) if (x,y,z)!=(0,0,0))
CUBE_INDEX={p:i for i,p in enumerate(PUNCTURED)}
assert len(PUNCTURED)==26


def sign(x):
    if not 0<=x<C.TOTAL:
        raise ValueError("index outside 196884")
    if x<C.FINE:
        chart,d=C.unpack(x)
        d=list(d)
        i=C.selected(chart)
        d[i]=(-d[i])%3
        return C.pack(chart,tuple(d))
    i=x-C.FINE
    if i in (0,1):
        return x
    return C.FINE+(i+26 if i<28 else i-26)


def coarse_d4(x,g):
    i=x-C.FINE
    if i in (0,1):
        return x
    branch,p=divmod(i-2,26)
    xx,yy,zz=PUNCTURED[p]
    if g=="rotation":
        transformed=(-yy,xx,zz)
    elif g=="reflection":
        transformed=(-xx,yy,zz)
    else:
        raise ValueError("D4 generator invalid")
    return C.FINE+2+branch*26+CUBE_INDEX[transformed]


def d4(x,g):
    if x>=C.FINE:
        return coarse_d4(x,g)
    if g not in ("rotation","reflection"):
        raise ValueError("D4 generator invalid")
    return C.d4(x,C.rot90 if g=="rotation" else C.reflect)


def receipt():
    assert C.COARSE==54==1+1+2*(27-1)
    for x in range(C.TOTAL):
        assert sign(sign(x))==x
        assert sign(C.c3(sign(x)))==C.c3(x,2)
        assert C.c3(x,3)==x
        for gen in ("rotation","reflection"):
            assert d4(sign(x),gen)==sign(d4(x,gen))
            assert d4(C.c3(x),gen)==C.c3(d4(x,gen))
    fixed_s=sum(sign(x)==x for x in range(C.TOTAL))
    fixed_r=sum(C.c3(x)==x for x in range(C.TOTAL))
    assert fixed_s==65612 and fixed_r==54
    m_trivial=(C.TOTAL+2*fixed_r+3*fixed_s)//6
    m_sign=(C.TOTAL+2*fixed_r-3*fixed_s)//6
    m_standard=(C.TOTAL-fixed_r)//3
    assert (m_trivial,m_sign,m_standard)==(65638,26,65610)
    assert m_trivial+m_sign+2*m_standard==C.TOTAL
    return dict(schema=1,source="DASHI pointed nine plus selected paired punctured 27",
      exhaustively_checked_basis_states=C.TOTAL,
      punctured_27_states=26, punctured_27_middle_plane=8,
      punctured_27_outer_planes=18,antipodal_punctured_27_orbits=13,
      coarse_53="one seam plus two oriented punctured 27",
      coarse_54="one invariant plus one seam plus two punctured 27",
      C3_character=[C.TOTAL,fixed_r,fixed_r],
      S3_reflection_character=fixed_s,
      S3_irreducible_multiplicities=dict(
          trivial=m_trivial,sign=m_sign,standard_2d=m_standard),
      c2_is_selected_trit_inversion_not_simultaneous_all_nine_trit_sign=True,
      involution_square_identity=True,conjugation_reverses_C3=True,
      selected_D4_generators_commute_with_C2_and_C3=True,
      geometric_six_by_nine_reduced_53_identification=False,
      published_FLM_3B_action_intertwiner=False,
      Griess_product_intertwiner=False).copy()


if __name__=="__main__":
    print(json.dumps(receipt(),sort_keys=True,indent=2))
