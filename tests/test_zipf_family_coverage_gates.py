"""Adversarial scope checks for the originally under-specified empirical subjects."""
from fractions import Fraction as F
from math import isclose
from pathlib import Path
import sys
import pytest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import zipf_family_coverage_gates as G
import zipf_family_formal as Z


def test_original_scope_has_27_disjoint_law_keys():
    expected={'zipf','one_percent','benford','bradford','brevity','demographic_gravitation','word_list','gibrat','hapax','heaps','hilberg','historical_recurrence','king','long_tail','lorenz','lotka','menzerath','pareto_distribution','pareto_principle','price','least_effort','rank_size','stigler','letter_frequency','common_english','zipf_mandelbrot','hurwitz'}
    assert {e.key for e in Z.ATLAS}==expected
    assert len(expected)==27


def test_three_tier_1percent_not_asserted_by_fiat():
    assert G.participation_roles([1]*4,[0,1,0,1],[0,0,1,0])==(F(1,4),F(1,2),F(1,4))
    assert G.participation_roles([0]*3,[0]*3,[0]*3)==(0,0,1)
    with pytest.raises(ValueError):G.participation_roles([1],[1,1],[0])


def test_benford_empirical_fraction_vs_expected():
    assert G.benford_observed_digits([1,10,2,-300])[:3]==(F(1,2),F(1,4),F(1,4))
    assert G.benford_observed_digits([1,2,3,4],2)==(F(1),)
    with pytest.raises(ValueError): G.benford_observed_digits([])


def test_bradford_exhaustive_optimal_zones_are_not_assumed_geometric():
    assert G.bradford_optimal_equal_zones([8,4,2,1],2)==((1,8),(3,7))
    assert sum(a for a,b in G.bradford_optimal_equal_zones([5,3,2],3))==3
    assert sum(b for a,b in G.bradford_optimal_equal_zones([5,3,2],3))==10
    with pytest.raises(ValueError): G.bradford_optimal_equal_zones([3,1],3)


def test_brevity_negative_and_positive_covariance_both_possible():
    assert G.type_level_brevity_covariance({'a':4,'bbbb':1},{'a':1,'bbbb':4})<0
    assert G.type_level_brevity_covariance({'a':1,'bbbb':4},{'a':1,'bbbb':4})>0
    with pytest.raises(ValueError):G.type_level_brevity_covariance({'a':1},{'b':2})


def test_gibrat_covariance_zero_does_not_imply_independence():
    assert G.gibrat_size_growth_covariance([(1,2),(2,4)])==0
    assert G.gibrat_size_growth_covariance([(1,1),(2,4)])>0
    assert G.gibrat_size_growth_covariance([(1,2),(2,2)])<0


def test_hilberg_block_entropy_not_a_rank_only_quantity():
    iid=['aa','ab','ba','bb']
    assert isclose(G.empirical_block_entropy(iid,1),2)
    assert G.empirical_block_entropy(['a']*8,4)==0
    assert G.empirical_block_entropy(['a','b','a','b'],2)>0
    with pytest.raises(ValueError):G.empirical_block_entropy(['a'],2)


def test_novelty_runs_distinguish_same_token_histogram():
    assert G.novelty_run_lengths(list('aabbcc'))!=G.novelty_run_lengths(list('abcabc'))


def test_menzerath_means_are_observed_and_nonmonotone_possible():
    assert G.menzerath_empirical_means([[10],[4,4],[3,3],[2,2,2]])==((1,F(10),1),(2,F(7,2),2),(3,F(2),1))
    assert G.menzerath_empirical_means([[1],[10,10]])[0][1]<G.menzerath_empirical_means([[1],[10,10]])[1][1]


def test_lotka_bibliometric_author_counts_support_zero_censoring():
    assert G.lotka_author_productivity({'a':0,'b':2,'c':2,'d':3})==((0,1),(2,2),(3,1))


def test_least_effort_observed_regret_does_not_establish_motive():
    assert G.observed_choice_regret({'a':F(2),'b':F(4)},'a')==0
    assert G.observed_choice_regret({'a':F(2),'b':F(4)},'b')==2


def test_stigler_priority_requires_two_document_roots():
    p=G.SourcePriority('Law X','Stigler','Newcomb','document-1881',1881,'name-1980',1980)
    assert G.documented_eponym_gap(p)
    p2=G.SourcePriority('Law X','Newcomb','Newcomb','document-1881',1881,'name-1882',1882)
    assert not G.documented_eponym_gap(p2)
    with pytest.raises(ValueError):G.documented_eponym_gap(G.SourcePriority('x','a','b','',1881,'name',1980))


def test_historical_recurrence_needs_coded_source_roots_and_dates():
    assert G.coded_historical_recurrence([(1901,'event','src1'),(1940,'event','src2')])==(('event',1901,1940,'src1','src2'),)
    assert G.coded_historical_recurrence([(1940,'event','src2'),(1901,'event','src1')])==()
    with pytest.raises(ValueError):G.coded_historical_recurrence([(1901,'event','')])
