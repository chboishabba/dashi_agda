#!/usr/bin/env python3
"""Exact C3-on-pointed-ternary-sheet permutation and D4 intertwiner witness.

Source owners: PointedTernaryBulkExact (one unmarked or one of nine marked
sites, with 3^9 trit assignments), Monster196884FibreInterferenceExact
(196830 + 54) and Monster3BC3RepresentationRingEvaluationExact.

C3 rotates the selected site trit on each sheet; for an unmarked
sheet the selected site is the D4-fixed centre. D4 permutes sheet
positions and the marker TOGETHER. The 54 coarse basis elements are
declared C3-fixed. Exact source-to-canonical C3 regular-orbit bijection
and D4 commuting law are verified exhaustively over ALL 196830 states.

Not an FLM/Monster-3B same-action intertwiner, a Griess product, a
Monster group action, or a representation on a trained Leech model.
"""
import json

N=9
N3=3**N
CHARTS=N+1
FINE=CHARTS*N3
COARSE=6*N
TOTAL=FINE+COARSE
ORBITS=CHARTS*3**(N-1)


def unpack(x):
    if not 0<=x<FINE:
        raise ValueError("original fine source index invalid")
    chart,val=divmod(x,N3)
    return chart,tuple((val//3**i)%3 for i in range(N))


def pack(chart,digits):
    if not 0<=chart<CHARTS or len(digits)!=N or any(z not in (0,1,2) for z in digits):
        raise ValueError("invalid original sheet or chart")
    return chart*N3+sum(z*3**i for i,z in enumerate(digits))


def selected(chart):
    if not 0<=chart<CHARTS:
        raise ValueError("chart invalid")
    return 4 if chart==0 else chart-1


def c3(x,power=1):
    if not 0<=x<TOTAL:
        raise ValueError("196884 index invalid")
    if x>=FINE:
        return x
    chart,d=unpack(x)
    d=list(d); i=selected(chart)
    d[i]=(d[i]+power)%3
    return pack(chart,tuple(d))


def to_regular(x):
    chart,d=unpack(x)
    i=selected(chart)
    residual=[d[j] for j in range(N) if j!=i]
    block=chart*3**(N-1)+sum(z*3**j for j,z in enumerate(residual))
    return block,d[i]


def from_regular(block,phase):
    if not 0<=block<ORBITS or phase not in (0,1,2):
        raise ValueError("regular orbit-phase invalid")
    chart,val=divmod(block,3**(N-1))
    i=selected(chart)
    rest=[(val//3**j)%3 for j in range(N-1)]
    return pack(chart,tuple(rest[:i]+[phase]+rest[i:]))


def rot90(i):
    row,col=divmod(i,3)
    return col*3+(2-row)


def reflect(i):
    row,col=divmod(i,3)
    return row*3+(2-col)


def d4(x,site_permutation):
    chart,d=unpack(x)
    out=[0]*N
    for i,z in enumerate(d):
        out[site_permutation(i)]=z
    return pack(0 if chart==0 else site_permutation(chart-1)+1,tuple(out))


def receipt():
    assert (FINE,COARSE,TOTAL,ORBITS)==(196830,54,196884,65610)
    assert rot90(4)==4 and reflect(4)==4
    for x in range(FINE):
        block,phase=to_regular(x)
        assert from_regular(block,phase)==x
        assert to_regular(c3(x))==(block,(phase+1)%3)
        assert c3(x,3)==x and c3(x)!=x and c3(x,2)!=x
        for action in (rot90,reflect):
            assert c3(d4(x,action))==d4(c3(x),action)
    for x in range(FINE,TOTAL):
        assert c3(x)==x and c3(x,2)==x
    # A permutation of an orthonormal basis is orthogonal.
    return dict(schema=1,exhaustive_states=FINE,dimension=TOTAL,
      free_fine_C3_orbits=ORBITS,coarse_fixed_basis=COARSE,
      C3_traces=[TOTAL,COARSE,COARSE],
      irreducible_multiplicities_C3=[ORBITS+COARSE,ORBITS,ORBITS],
      selected_marker_trit_action_is_order_three=True,
      D4_commutation_for_full_fine_sheet=True,
      canonical_regular_block_intertwiner_verified=True,
      source_original_Griess_product_preserved=None,
      agrees_with_published_FLM_3B_action=None,
      D4_coarse_54_action_unselected=True)


if __name__=="__main__":
    print(json.dumps(receipt(),sort_keys=True,indent=2))
