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
