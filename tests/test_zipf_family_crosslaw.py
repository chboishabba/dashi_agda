"""Cross-law adversarial regressions: shared ranks are NOT joint-law proofs."""
import math,sys
from fractions import Fraction
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import zipf_family_formal as Z

def test_same_zipf_histogram_different_heaps_trajectories():
    grouped=['a','a','b','b','c','c']
    interleaved=['a','b','c','a','b','c']
    assert Z.word_list(grouped)==Z.word_list(interleaved)
    assert Z.heaps_prefix(grouped)==(1,1,2,2,3,3)
    assert Z.heaps_prefix(interleaved)==(1,2,3,3,3,3)
    assert Z.heaps_prefix(grouped)!=Z.heaps_prefix(interleaved)

def test_heaps_prefix_is_one_lipschitz_and_bounded_by_corpus_length():
    for tokens in ([],['a'],['a','a','a'],['x','y','x','z','y']):
        v=(0,)+Z.heaps_prefix(tokens)
        assert all(d in (0,1) for d in (b-a for a,b in zip(v,v[1:])))
        assert all(x<=i for i,x in enumerate(v))
        assert v[-1]==len(Z.word_list(tokens))

def test_zipf_histogram_does_not_imply_benford_digit_frequencies():
    counts=[12,6,4,3]
    assert [Fraction(x,counts[0]) for x in counts]==[Fraction(1,r) for r in range(1,5)]
    first=[Z.leading_digit(x) for x in counts]
    assert first==[1,6,4,3]
    assert first.count(1)/len(first)!=Z.benford_first_digit(10,1)

def test_hurwitz_shifted_finite_head_tail_is_exact_rational():
    for s in (0,1,2,5):
        for q in (0,1,3):
            for n in (0,1,3):
                m=5
                assert Z.finite_hurwitz(s,q,n+m)==Z.finite_hurwitz(s,q,n)+Z.finite_hurwitz(s,q+n,m)

def test_zipf_mandelbrot_is_monotone_for_positive_exponent():
    for s in (.1,.5,1.,3.):
        for q in (0,1,10):
            masses=Z.zipf_mandelbrot(20,s,q)
            assert all(a>b for a,b in zip(masses,masses[1:]))
            assert math.isclose(sum(masses),1)

def test_scale_and_permutation_invariance_of_lorenz_gini():
    x=[1,4,2,0,9]
    y=[9,0,2,4,1]
    z=[3*v for v in x]
    assert Z.lorenz_curve(x)==Z.lorenz_curve(y)==Z.lorenz_curve(z)
    assert math.isclose(Z.gini(x),Z.gini(y))
    assert math.isclose(Z.gini(x),Z.gini(z))

def test_pareto_survival_conditional_scaling():
    for alpha in (.5,1.,3.):
        assert math.isclose(Z.pareto_survival(6,1,alpha)/Z.pareto_survival(2,1,alpha),3**(-alpha))

def test_king_ratio_changes_with_baseline_exponent_not_only_the_data():
    values=[100,20,10,5]
    assert Z.king_effect_ratio(values,0)==5
    assert Z.king_effect_ratio(values,1)==2.5
    assert Z.king_effect_ratio(values,2)==1.25

def test_gibrat_same_growth_ratio_cannot_determine_population_levels():
    assert Z.gibrat_growth_ratios([1,2,4])==Z.gibrat_growth_ratios([100,200,400])
    assert Z.demographic_gravity(1,2,2)!=Z.demographic_gravity(100,200,2)

def test_benford_base_change_is_not_fixed_digit_probability():
    assert not math.isclose(Z.benford_first_digit(10,1),Z.benford_first_digit(2,1))
    assert math.isclose(Z.benford_first_digit(2,1),1)

def test_frequency_ties_require_stable_lexicographic_rank_rule():
    assert Z.word_list(['b','a'])==(('a',1),('b',1))
    assert Z.word_list(['a','b'])==(('a',1),('b',1))

def test_powerlaw_models_do_not_force_half_by_sqrt_authors():
    equal=[1]*16
    assert Z.price_sqrt_top_count(len(equal))==4
    assert Z.price_share(equal)==.25
    assert Z.top_share(equal,4)==.25
