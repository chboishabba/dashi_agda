"""Exact no-universal-fit checks over a fixed rank dictionary."""
from fractions import Fraction as F
from pathlib import Path
import sys
import pytest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from zipf_heaps_bridge import finite_rank_probabilities
import zipf_rank_model_evidence_exact as E


def test_exact_truncated_geometric_normalization_and_limit():
    assert E.finite_geometric_probabilities(4,F(1,4))==(F(64,85),F(16,85),F(4,85),F(1,85))
    assert E.finite_geometric_probabilities(4,F(1))==(F(1,4),)*4
    with pytest.raises(ValueError):E.finite_geometric_probabilities(4,F(0))


def test_predeclared_geometric_can_outscore_zipf_on_exact_heldout_data():
    counts=(64,16,4,1)
    geom=E.finite_geometric_probabilities(4,F(1,4))
    zipf1=finite_rank_probabilities(4,1,0)
    zipf2=finite_rank_probabilities(4,2,0)
    model,value=E.select_finite_rank_model(counts,(
        ('zipf-s1',zipf1),('geometric-q-quarter',geom),('zipf-s2',zipf2)))
    assert model=='geometric-q-quarter'
    assert value>E.exact_rank_likelihood(counts,zipf1)
    assert value>E.exact_rank_likelihood(counts,zipf2)


def test_exact_zipf_sample_can_outscore_geometric_alternative():
    counts=(60,30,20)
    zipf=finite_rank_probabilities(3,1,0)
    geom=E.finite_geometric_probabilities(3,F(1,2))
    assert E.exact_rank_likelihood(counts,zipf)>E.exact_rank_likelihood(counts,geom)


def test_unseen_positive_tail_not_logical_absence():
    p=finite_rank_probabilities(5,2,1)
    assert 0<E.exact_unseen_tail_probability(p,2,3)<1
    assert E.exact_unseen_tail_probability(p,2,0)==1
    assert E.exact_unseen_tail_probability(p,5,100)==1
    assert E.exact_unseen_tail_probability(p,0,1)==0


def test_zero_observations_is_not_universal_model_evidence():
    models=(('g',E.finite_geometric_probabilities(3,F(1,2))),
            ('z',finite_rank_probabilities(3,1,0)))
    with pytest.raises(ValueError, match='no held-out observations'):
        E.select_finite_rank_model((0,0,0),models)


def test_zero_likelihood_does_not_get_logged_or_divided():
    assert E.exact_rank_likelihood((0,0,1),(F(1),F(0),F(0)))==0
    assert E.exact_rank_likelihood((1,0,0),(F(1),F(0),F(0)))==1
    with pytest.raises(ValueError): E.exact_rank_likelihood((1,1),(F(1),))


def test_rank_provenance_and_independence_are_explicit_inputs():
    gate=E.FixedRankEvidence('corpus-sha','rank-map-v1','train-ids','test-ids',True,True)
    assert E.admit_rank_likelihood(gate)
    assert not E.admit_rank_likelihood(E.FixedRankEvidence('corpus-sha','rank-map-v1','same','same',True,True))
    assert not E.admit_rank_likelihood(E.FixedRankEvidence('corpus-sha','rank-map-v1','train','test',False,True))
    assert not E.admit_rank_likelihood(E.FixedRankEvidence('corpus-sha','rank-map-v1','train','test',True,False))
