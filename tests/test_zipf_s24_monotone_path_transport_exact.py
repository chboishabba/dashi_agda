"""Exact joint-path Strassen/flow certificates; no kernel claim."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import sys
import pytest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"scripts"))
from zipf_heaps_bridge import multiset_count_majorizes
from zipf_s24_monotone_path_transport_exact import (
    _transport_maxflow, PathTransportCertificate,
    majorization_heaps_path_transport_certificate,
)


def test_all_small_two_and_three_type_majorization_pairs_have_full_path_flow():
    validated=0
    for k in (2,3):
        candidates=list(product((1,2,3),repeat=k))
        for a in candidates:
            for b in candidates:
                if sum(a)!=sum(b) or not multiset_count_majorizes(a,b):
                    continue
                t=sum(a)
                for sampler in ("iid","permutation"):
                    cert=majorization_heaps_path_transport_certificate(
                        a,b,t,sampler)
                    cert.validate()
                    assert cert.matched_mass==F(1)
                    validated+=1
    assert validated==268


def test_all_prefixes_remain_coordinatewise_monotone_in_one_joint_coupling():
    for a,b in (((3,1,1),(2,2,1)),((4,1,1),(2,2,2)),
                ((5,1,1),(3,2,2)),((3,1),(2,2))):
        for sampler in ("iid","permutation"):
            cert=majorization_heaps_path_transport_certificate(
                a,b,sum(a),sampler)
            for (left,right),weight in cert.coupling.items():
                assert weight>0 and all(x<=y for x,y in zip(left,right))
            assert sum(cert.coupling.values(),F())==1


def test_same_histogram_has_diagonal_transport_witness():
    for c in ((1,1),(2,1),(3,2,1),(1,1,1)):
        for sampler in ("iid","permutation"):
            cert=majorization_heaps_path_transport_certificate(c,c,sum(c),sampler)
            assert cert.left_law==cert.right_law
            assert all(left==right for left,right in cert.coupling)


def test_exact_transport_detects_non_dominance_not_fabricated_receipt():
    # Left is certainly above right at t=2: no coordinatewise <= coupling.
    left={(0,1,2):F(1)}
    right={(0,1,1):F(1)}
    flow,coupling=_transport_maxflow(left,right)
    assert flow==0 and coupling=={}
    # The opposite orientation admits a unit coupling.
    flow,coupling=_transport_maxflow(right,left)
    assert flow==1 and coupling=={((0,1,1),(0,1,2)):F(1)}


def test_transport_is_a_real_2_by_2_fractional_mass_split():
    left={(0,1,1):F(1,2),(0,1,2):F(1,2)}
    right={(0,1,1):F(1,4),(0,1,2):F(3,4)}
    flow, coupling=_transport_maxflow(left,right)
    assert flow==1
    cert=PathTransportCertificate((2,1),(1,2),"iid",2,
                                  left,right,coupling,flow)
    cert.validate()
    assert coupling[(0,1,1),(0,1,1)]==F(1,4)
    assert coupling[(0,1,1),(0,1,2)]==F(1,4)


def test_fail_closed_on_bad_domains_and_resource_caps():
    with pytest.raises(ValueError):
        majorization_heaps_path_transport_certificate((2,2),(3,1),2,"iid")
    with pytest.raises(ValueError):
        majorization_heaps_path_transport_certificate((2,1),(2,1),True,"iid")
    with pytest.raises(ValueError):
        majorization_heaps_path_transport_certificate((2,1),(2,1),4,"permutation")
    with pytest.raises(ValueError):
        majorization_heaps_path_transport_certificate((2,1),(2,1),2,"wrong")
    with pytest.raises(ValueError):
        _transport_maxflow({(0,):F(1)}, {(0,):F(1)},max_edges=0)
    with pytest.raises(ValueError):
        _transport_maxflow({(0,):F(1)}, {(0,):F(1)},max_edges=True)
    with pytest.raises(ValueError):
        _transport_maxflow({(0,):F(1,2)}, {(0,):F(1)})
    with pytest.raises(ValueError):
        _transport_maxflow({(0,):F(1)}, {(0,):F(1)},max_edges=0)


def test_source_provenance_and_no_new_probability_carrier():
    src=(ROOT/"scripts/zipf_s24_monotone_path_transport_exact.py").read_text()
    assert "from zipf_full_heaps_path_distribution_exact import full_heaps_curve_law" in src
    assert "from zipf_heaps_bridge import _validated_counts, multiset_count_majorizes" in src
    assert "Strassen" in src and "Hardy-Littlewood-Polya" in src
    assert "Agda kernel" in src and "not a general theorem" in src.lower()


def test_equal_every_coordinate_marginal_does_not_supply_a_path_coupling():
    # Four *valid* discovery curves with binary 0/1 increments and V0=0:
    # X: half of lower/lower and upper/upper.
    # Y: half of lower/upper and upper/lower.
    # Each coordinate V_t has the SAME law under X and Y, yet the joint
    # path laws differ and only half the mass admits monotone transport.
    lo_lo=(0,1,1,2,2)
    hi_hi=(0,1,2,2,3)
    lo_hi=(0,1,1,2,3)
    hi_lo=(0,1,2,2,2)
    x={lo_lo:F(1,2),hi_hi:F(1,2)}
    y={lo_hi:F(1,2),hi_lo:F(1,2)}
    for t in range(5):
        assert {v:sum((p for curve,p in x.items() if curve[t]==v),F())
                for v in (0,1,2,3)} == {
                    v:sum((p for curve,p in y.items() if curve[t]==v),F())
                    for v in (0,1,2,3)}
    for law in (x,y):
        assert all(all(v-u in (0,1) for u,v in zip(curve,curve[1:]))
                   for curve in law)
    mass,flow=_transport_maxflow(x,y)
    assert mass==F(1,2) and sum(flow.values(),F())==F(1,2)


def test_dual_hall_cut_exactly_explains_marginal_equality_no_go():
    from zipf_s24_monotone_path_transport_exact import finite_hall_cut_obstruction
    x={(0,1,1,2,2):F(1,2),(0,1,2,2,3):F(1,2)}
    y={(0,1,1,2,3):F(1,2),(0,1,2,2,2):F(1,2)}
    cut=finite_hall_cut_obstruction(x,y)
    assert cut is not None
    a,up,delta=cut
    assert delta==F(1,2)
    assert sum((x[z] for z in a),F())-sum((y[z] for z in up),F())==delta
    assert all(not (len(z)==len(right)
                    and all(v<=w for v,w in zip(z,right)))
               for z in a if z==(0,1,2,2,3) for right in y)


def test_dual_hall_cut_is_absent_for_true_majorization_couplings():
    from zipf_s24_monotone_path_transport_exact import finite_hall_cut_obstruction
    for sampler in ("iid","permutation"):
        cert=majorization_heaps_path_transport_certificate((3,1,1),(2,2,1),5,sampler)
        assert finite_hall_cut_obstruction(cert.left_law,cert.right_law)==None
    with pytest.raises(ValueError):
        finite_hall_cut_obstruction({(0,):F(1)}, {(0,):F(1)},max_left_paths=True)


def test_all_pair_transfer_first_switch_probabilities_exact():
    from zipf_s24_monotone_path_transport_exact import (
        pair_one_type_survival_probability, concentrating_pair_transfer_certificate)
    from math import comb
    checked=0
    for b in range(2,8):
        for a in range(b,9):
            for m in range(a+b+1):
                cert=concentrating_pair_transfer_certificate(a,b,m)
                for sampler,(original,concentrated) in cert.items():
                    assert original<=concentrated
                    if m==0:
                        assert original==concentrated==1
                    elif sampler=="iid":
                        assert original==F(a,a+b)**m+F(b,a+b)**m
                    else:
                        assert original==F(comb(a,m)+comb(b,m),comb(a+b,m))
                    checked+=1
    assert checked>500
    for bad in ((0,2,0,"iid"),(3,0,0,"iid"),(2,1,1,"bad"),
                (2,1,-1,"iid"),(2,1,4,"permutation")):
        with pytest.raises(ValueError):
            pair_one_type_survival_probability(*bad)


def test_pair_transfer_premises_reject_non_concentrating_boundary():
    from zipf_s24_monotone_path_transport_exact import concentrating_pair_transfer_certificate
    for a,b,m in ((2,1,0),(1,2,1),(1,1,1),
                  (3,2,-1),(3,2,6),(True,2,0)):
        with pytest.raises(ValueError):
            concentrating_pair_transfer_certificate(a,b,m)


def test_permutation_pair_pascal_difference_exhaustive_grid():
    from zipf_s24_monotone_path_transport_exact import exact_permutation_pair_transfer_difference
    from math import comb
    checks=0
    for b in range(2,8):
        for a in range(b,9):
            for m in range(a+b+1):
                difference=exact_permutation_pair_transfer_difference(a,b,m)
                if m==0:
                    assert difference==0
                else:
                    assert difference==F(comb(a,m-1)-comb(b-1,m-1),comb(a+b,m))
                    assert difference>=0
                checks+=1
    assert checks==291
    for bad in ((1,2,0),(3,1,1),(3,2,-1),(3,2,6)):
        with pytest.raises(ValueError):
            exact_permutation_pair_transfer_difference(*bad)
