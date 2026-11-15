"""Source-rooted bounded word-frequency acceptance; no full-corpus inference."""
from fractions import Fraction as F
from pathlib import Path
import sys
import pytest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from zipf_heaps_bridge import finite_rank_probabilities
from zipf_rank_model_evidence_exact import finite_geometric_probabilities
import zipf_clauset_words30_source_receipt as W


def test_primary_catalogue_head_is_fingerprinted_not_undated_synthetic():
    assert W.SOURCE_URL.endswith('/powerlaws/data/words.txt')
    assert len(W.FIRST_30)==30
    assert sum(W.FIRST_30)==75648
    assert W.FIRST_30[:5]==(14086,6414,6260,4573,4484)
    assert all(a>=b for a,b in zip(W.FIRST_30,W.FIRST_30[1:]))
    assert W.prefix_fingerprint(W.FIRST_30)==W.PREFIX_SHA256


def test_conditional_head_mass_is_not_a_whole_corpus_fraction():
    p=W.conditional_head_distribution(W.FIRST_30)
    assert len(p)==30 and sum(p,F())==1
    assert p[0]==F(14086,75648)
    assert p[-1]==F(844,75648)


def test_head_only_geometric_ratio_point_nine_outscores_integer_zipf_one_by_cdf():
    # Exploratory candidate comparison only; models were not preregistered,
    # no held-out selection, no likelihood p-value or full-corpus fit.
    geo=finite_geometric_probabilities(30,F(9,10))
    zipf=finite_rank_probabilities(30,1,0)
    dg=W.rank_head_cdf_distance(W.FIRST_30,geo)
    dz=W.rank_head_cdf_distance(W.FIRST_30,zipf)
    assert dg<dz
    assert F(8,100)<dg<F(9,100)
    assert F(10,100)<dz<F(11,100)


def test_empirical_head_is_not_exactly_zipf_or_geometric():
    p=W.conditional_head_distribution(W.FIRST_30)
    assert p!=finite_rank_probabilities(30,1,0)
    assert p!=finite_geometric_probabilities(30,F(9,10))


def test_failure_on_mismatched_fingerprint_or_mass_domain():
    assert W.prefix_fingerprint(W.FIRST_30[:-1]) != W.PREFIX_SHA256
    with pytest.raises(ValueError):W.conditional_head_distribution([0,0])
    with pytest.raises(ValueError):W.rank_head_cdf_distance([1,2],[F(1)])
