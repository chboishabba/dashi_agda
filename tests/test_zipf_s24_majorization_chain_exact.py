"""S24 constructive HLP chain and gluing; exact finite regression.

Executed locally on byte-identical new scripts with small independent
word-enumeration dependency oracles. No Agda kernel or CI claim.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import sys
import pytest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"scripts"))
from zipf_heaps_bridge import multiset_count_majorizes
from zipf_s24_majorization_chain_exact import (
    positive_majorization_transfer_chain,
    constructive_majorization_path_certificate,
    glue_monotone_path_certificates,
)
from zipf_s24_pair_switch_constructive_exact import (
    constructive_pair_transfer_path_certificate,
)


def test_804_small_majorization_transports_are_constructive_not_flow_searches():
    checked=0
    for k in (2,3):
        candidates=list(product((1,2,3),repeat=k))
        for f in candidates:
            for g in candidates:
                if sum(f)!=sum(g) or not multiset_count_majorizes(f,g):
                    continue
                chain=positive_majorization_transfer_chain(f,g)
                for before,pair,after in chain:
                    a,b=pair
                    assert before[a]>=before[b]>=2
                    mutated=tuple(x+(1 if i==a else -1 if i==b else 0)
                                  for i,x in enumerate(before))
                    assert tuple(sorted(mutated,reverse=True))==after
                for sampler in ("iid","permutation"):
                    for t in (0,2,min(sum(f),4)):
                        receipt=constructive_majorization_path_certificate(
                            f,g,t,sampler)
                        receipt.validate()
                        assert receipt.matched_mass==F(1)
                        assert all(all(x<=y for x,y in zip(left,right))
                                   for left,right in receipt.coupling)
                        checked+=1
    assert checked==804


def test_nontrivial_hlp_chain_and_exact_gluing():
    concentrated=(4,1,1)
    dispersed=(2,2,2)
    chain=positive_majorization_transfer_chain(concentrated,dispersed)
    assert len(chain)==2
    for sampler in ("iid","permutation"):
        cert=constructive_majorization_path_certificate(
            concentrated,dispersed,5,sampler)
        assert sum(cert.coupling.values(),F())==1
        assert len(cert.coupling)>1
        cert.validate()


def test_permutation_of_type_labels_needs_no_new_probability_carrier():
    for f in ((3,2,1),(2,2,1),(1,1,1)):
        g=tuple(reversed(f))
        assert positive_majorization_transfer_chain(f,g)==()
        for sampler in ("iid","permutation"):
            receipt=constructive_majorization_path_certificate(
                f,g,sum(f),sampler)
            receipt.validate()
            assert all(x==y for x,y in receipt.coupling)


def test_gluing_requires_same_intermediate_path_law_and_model():
    first=constructive_pair_transfer_path_certificate((2,2,1),(0,1),3,"iid")
    second=constructive_pair_transfer_path_certificate((2,2,1),(0,1),4,"iid")
    with pytest.raises(ValueError):
        glue_monotone_path_certificates(first,second)
    other=constructive_pair_transfer_path_certificate((2,2,1),(0,1),3,"permutation")
    with pytest.raises(ValueError):
        glue_monotone_path_certificates(first,other)


def test_reverse_majorization_and_invalid_resource_limits_fail_closed():
    with pytest.raises(ValueError):
        positive_majorization_transfer_chain((2,2,2),(4,1,1))
    with pytest.raises(ValueError):
        positive_majorization_transfer_chain((4,1,1),(2,2,2),max_states=1)
    with pytest.raises(ValueError):
        positive_majorization_transfer_chain((4,1,1),(2,2,2),max_states=True)
    with pytest.raises(ValueError):
        constructive_majorization_path_certificate((4,1,1),(2,2,2),7,"permutation")
    with pytest.raises(ValueError):
        constructive_majorization_path_certificate((4,1,1),(2,2,2),True,"iid")


def test_code_reuses_source_owners_and_never_claims_kernel_validation():
    src=(ROOT/"scripts/zipf_s24_majorization_chain_exact.py").read_text()
    assert "from zipf_s24_pair_switch_constructive_exact import constructive_pair_transfer_path_certificate" in src
    assert "from zipf_s24_monotone_path_transport_exact import PathTransportCertificate" in src
    assert "NOT an Agda kernel theorem" in src
    assert "postulate" not in src
