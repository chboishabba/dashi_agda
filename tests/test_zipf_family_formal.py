"""27-subject finite mathematical regression and nonpromotion gates."""
import math,sys
from fractions import Fraction
from pathlib import Path
import pytest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import zipf_family_formal as Z

def test_27_distinct_typed_entries():
    assert len(Z.ATLAS)==27
    assert len(set(e.name for e in Z.ATLAS))==27
    assert len(set(e.key for e in Z.ATLAS))==27
    assert {a.value for a in Z.Authority}==set(e.authority.value for e in Z.ATLAS)
    assert Z.proof_status('stigler')==Z.Authority.PROVENANCE

def test_zipf_exact_finite_normalization_and_shift_specialization():
    p=Z.zipf_mandelbrot(5,1,0)
    assert math.isclose(sum(p),1)
    assert all(a>b for a,b in zip(p,p[1:]))
    assert Z.zipf_mandelbrot(4,0,3)==(.25,)*4
    assert Z.zipf_mandelbrot(4,2,0)==Z.zipf_mandelbrot(4,2)
    assert Z.finite_hurwitz(1,0,5)==Fraction(137,60)

def test_zipf_shift_never_artificially_equals_unshifted():
    assert Z.zipf_mandelbrot(5,1,3)!=Z.zipf_mandelbrot(5,1,0)
    with pytest.raises(ValueError): Z.zipf_mandelbrot(0,1)
    with pytest.raises(ValueError): Z.zipf_mandelbrot(2,1,-1)

def test_hurwitz_tail_rigorous_integral_bounds():
    # T_n(q,s)=sum_{r=n+1}^infinity (r+q)^(-s). Old test wrongly
    # evaluated sum from 6 while q=1 implies the first denominator is 7.
    for s,q,n in ((2,1,5),(2,0,5),(3,10,8),(4,2,4)):
        lower,upper=Z.hurwitz_tail_bound(s,q,n)
        independent_partial=sum(1/(r+q)**s for r in range(n+1,100000))
        # The omitted tail is positive and below integral_{99999}^infinity.
        omitted_upper=(99999+q)**(1-s)/(s-1)
        assert lower < independent_partial
        assert independent_partial+omitted_upper < upper
    with pytest.raises(ValueError): Z.hurwitz_tail_bound(1,1,5)
    with pytest.raises(ValueError): Z.hurwitz_tail_bound(2,-1,5)

def test_one_percent_rule_is_an_observation_not_a_numeric_identity():
    assert Z.participation_shares([0]*99+[2])==(.01,.99)
    assert Z.participation_shares([1]*100)==(1.,0.)
    with pytest.raises(ValueError): Z.participation_shares([])

def test_benford_digits_normalize_and_nonuniversality():
    d=[Z.benford_first_digit(10,k) for k in range(1,10)]
    assert math.isclose(sum(d),1,abs_tol=1e-12)
    assert d[0]>d[1]>d[-1]
    assert Z.leading_digit(.00314159)==3
    assert Z.leading_digit(-456)==4
    assert Z.leading_digit(15,2)==1
    with pytest.raises(ValueError): Z.leading_digit(0)

def test_bradford_scattering_zone_model_vs_actual_diagnostic():
    assert Z.bradford_zone_sizes(2,3,3)==(2,6,18)
    zones=Z.bradford_empirical_zones([12,6,3,2,1],2)
    assert sum(a for a,b in zones)==5
    assert sum(b for a,b in zones)==24

def test_brevity_uses_lengths_and_empirical_counts_without_assuming_correlation():
    assert Z.brevity_pairs(['a','a','bb'],{'a':1,'bb':2})==((1,2),(2,1))
    assert Z.brevity_pairs(['a','b','b'],{'a':1,'b':2})==((1,1),(2,2))

def test_demographic_gravity_inverse_distance_model():
    assert Z.demographic_gravity(10,20,2)==50
    assert Z.demographic_gravity(10,20,4)==12.5
    with pytest.raises(ValueError): Z.demographic_gravity(1,1,0)

def test_word_lists_hapax_and_token_counts_are_operational():
    tokens=['b','a','b','c','a','a']
    assert Z.word_list(tokens)==(('a',3),('b',2),('c',1))
    assert Z.hapaxes(tokens)==('c',)
    assert Z.corpus_counts(tokens)['a']==3

def test_gibrat_proportional_growth_can_appear_or_fail():
    assert Z.gibrat_growth_ratios([1,2,4])==(2.,2.)
    assert Z.gibrat_growth_ratios([1,2,3])!=(2.,2.)

def test_heaps_prefix_is_exact_and_sublinear_model_not_forced():
    assert Z.heaps_prefix(['a','a','b','a','c'])==(1,1,2,2,3)
    assert Z.heaps_model(16,2,.5)==8
    assert Z.heaps_prefix(['a']*10)[-1]==1

def test_hilberg_entropy_power_is_only_parameterized():
    assert Z.hilberg_model(16,3,.5)==12
    assert Z.proof_status('hilberg')==Z.Authority.HYPOTHESIS

def test_historical_recurrence_is_observer_coded():
    assert Z.repeated_event_pairs([(1900,'a'),(1950,'b'),(2000,'a')])==((1900,2000,'a'),)
    assert Z.repeated_event_pairs([(1900,'a'),(2000,'b')])==()

def test_king_effect_requires_model_and_is_not_automatic():
    assert Z.king_effect_ratio([100,10,5],1)==5
    assert Z.king_effect_ratio([20,10,5],1)==1

def test_long_tail_and_lorenz_gini_exact_normalization():
    assert Z.long_tail_share([4,3,2,1],1)==.6
    curve=Z.lorenz_curve([1,1,1,1])
    assert curve[0]==(0,0) and curve[-1]==(1.,1.)
    assert Z.gini([1,1,1,1])==0
    assert math.isclose(Z.gini([0,0,0,1]),.75)
    with pytest.raises(ValueError): Z.lorenz_curve([0,0])

def test_lotka_productivity_is_distribution_over_productivity_not_rank():
    assert Z.lotka_pmf(1,2,3)>Z.lotka_pmf(2,2,3)
    assert math.isclose(sum(Z.lotka_pmf(n,2,5) for n in range(1,6)),1)

def test_menzerath_altmann_has_parameters_not_universal_downward_slope():
    assert math.isclose(Z.menzerath_altmann(2,1,-1,0),.5)
    assert Z.menzerath_altmann(2,1,1,0)>Z.menzerath_altmann(1,1,1,0)

def test_pareto_distribution_normalization_cdf_and_survival():
    assert Z.pareto_cdf(1,1,2)==0
    assert Z.pareto_survival(2,1,2)==.25
    assert Z.pareto_cdf(2,1,2)==.75
    assert Z.pareto_cdf(0,1,2)==0
    with pytest.raises(ValueError): Z.pareto_survival(1,0,2)

def test_pareto_principle_80_20_has_counterexample():
    assert Z.top_share([4,1,1,1,1],1)==.5
    assert Z.top_share([80,5,5,5,5],1)==.8
    assert Z.top_share([1]*5,1)==.2

def test_price_sqrt_is_only_a_descriptive_threshold():
    assert Z.price_sqrt_top_count(9)==3
    assert Z.price_sqrt_top_count(10)==4
    assert Z.price_share([1]*9)==1/3
    assert Z.price_share([9,0,0,0,0,0,0,0,0])==1

def test_least_effort_optimum_is_not_claim_about_real_agents():
    assert Z.least_effort_argmins({'a':4,'b':1,'c':1})==('b','c')
    assert Z.proof_status('least_effort')==Z.Authority.HYPOTHESIS

def test_rank_size_is_not_power_law_by_definition():
    assert Z.rank_size([3,1,2])==(3,2,1)
    assert Z.rank_size([10,1,1])!=(10,5,10/3)

def test_stigler_attribution_mismatch_nonuniversality():
    a=Z.DiscoveryAttribution('test','late','early','original-document-1')
    b=Z.DiscoveryAttribution('test','early','early','original-document-2')
    assert Z.stigler_mismatch(a) and not Z.stigler_mismatch(b)

def test_letter_frequency_specifies_language_corpus():
    assert Z.letter_frequencies('AbBa!')['a']==2
    assert Z.letter_frequencies('AbBa!')['b']==2
    assert Z.letter_frequencies('abc',alphabet='a')=={'a':1}

def test_common_english_is_corpus_specific():
    assert Z.common_words(['the','cat','the','dog'],2)==(('the',2),('cat',1))
    assert Z.common_words(['cat','cat','the'],1)==(('cat',2),)

def test_research_family_no_unchecked_promotion():
    mathematical={e.key for e in Z.ATLAS if e.authority==Z.Authority.MATHEMATICAL}
    assert 'hapax' in mathematical and 'lorenz' in mathematical
    assert 'historical_recurrence' not in mathematical
    assert 'one_percent' not in mathematical
    assert 'stigler' not in mathematical
