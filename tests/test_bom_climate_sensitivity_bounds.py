"""Exact rational sensitivity scenarios for fewer-than-200 ACORN daily duplicates.

Scope: illustrative equal-weight *raw-observation* statistics. Real ACORN
uses station/gridded aggregation and homogenisation. These functions are NOT
the Bureau's actual published temperature or trend recomputation.
"""
from fractions import Fraction

DAILY_VALUE_UPPER_COUNT = 200
DATASET_LOWER_SIZE = 7_000_000
ILLUSTRATIVE_STATIONS = 112
ILLUSTRATIVE_YEARS = 116


def equally_weighted_mean_error_bound(
    wrong: int, n: int, max_abs_delta_c: int
) -> Fraction:
    assert 0 <= wrong <= n and n > 0 and max_abs_delta_c >= 0
    return Fraction(wrong * max_abs_delta_c, n)


def equally_weighted_ols_century_slope_error_approx(
    wrong: int, n: int, max_abs_delta_c: int, span_years: int
) -> Fraction:
    """Maximum centred time leverage, approx uniform annual timestamps.

    This assumes ALL errors have same sign and sit at earliest/latest time.
    It uses Var(t) ~= span_years**2/12: only an equal-weight regression toy.
    """
    assert span_years > 0
    return Fraction(600 * wrong * max_abs_delta_c, n * span_years)


def one_bad_station_month_national_annual_scenario(
    monthly_mean_diff_c: int, station_count: int
) -> Fraction:
    """If 12 months and all stations have equal annual aggregation weights."""
    assert station_count > 0
    return Fraction(monthly_mean_diff_c, 12 * station_count)


def test_extreme_uniform_mean_bound():
    assert equally_weighted_mean_error_bound(200, 7_000_000, 10) == Fraction(1, 3500)
    assert equally_weighted_mean_error_bound(200, 7_000_000, 50) == Fraction(1, 700)
    assert equally_weighted_mean_error_bound(200, 7_000_000, 2) == Fraction(1, 17500)


def test_only_tiny_fraction_of_total_values():
    assert Fraction(200, 7_000_000) == Fraction(1, 35_000)
    assert Fraction(200, 7_000_000) * 100 == Fraction(1, 350)


def test_illustrative_trend_max_leverage():
    # Less than 0.0015 C / century for <=200 10 C raw-entry errors
    # under a uniformly sampled 116-year unweighted raw-value OLS toy.
    assert equally_weighted_ols_century_slope_error_approx(
        200, 7_000_000, 10, 116
    ) < Fraction(15, 10_000)


def test_single_station_month_local_vs_national_scope():
    # Even a 2 C error across an *entire month* can affect the one
    # station's monthly mean by 2 C; annualising and averaging over 112
    # hypothetical identically weighted stations changes the scale.
    assert one_bad_station_month_national_annual_scenario(
        2, ILLUSTRATIVE_STATIONS
    ) == Fraction(1, 672)


def test_bound_requires_weights_and_correction_magnitudes():
    # Cannot promote this example to a bound on the actual gridded ACORN
    # dataset without per-observation station weights and true deltas.
    assert equally_weighted_mean_error_bound(200, 7_000_000, 50) < Fraction(1, 100)


def round_whole_degree_from_tenths(observed_tenths: int) -> int:
    """Positive Celsius temperatures rounded to nearest whole degree.

    This is a constructed instrument-resolution illustration, NOT the actual
    Palmerville 2004 recording transformation or climate series.
    """
    assert observed_tenths >= 0
    return (observed_tenths + 5) // 10


def test_seventeen_identical_rounded_days_do_not_identify_latent_tenths():
    """A single reported 31 C block can arise from varied exact histories."""
    exact_constant = [310] * 17
    exact_varied = [306, 314] + [310] * 15
    assert len(exact_constant) == len(exact_varied) == 17
    assert exact_constant != exact_varied
    assert tuple(map(round_whole_degree_from_tenths, exact_constant)) == (31,) * 17
    assert tuple(map(round_whole_degree_from_tenths, exact_varied)) == (31,) * 17
    # This disproves unique inverse recovery; it supplies NO probability
    # estimate for 17 actual Palmerville daily maxima.


def test_integer_precision_preserves_a_nontrivial_degree_bin():
    assert [round_whole_degree_from_tenths(x) for x in range(305, 315)] == [31] * 10
    assert round_whole_degree_from_tenths(304) == 30
    assert round_whole_degree_from_tenths(315) == 32
