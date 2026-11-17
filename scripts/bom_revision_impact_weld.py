#!/usr/bin/env python3
"""Source-bounded publication-version station/month impact from native BOM exports.

Uses the existing native integrity parser and the existing exact annual-panel
trend owner. A missing daily value, missing calendar row or multi-day rainfall
accumulation precludes a full-month observed difference. NO imputation.
Does NOT certify original paper observations, ACORN-SAT or national trends.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from fractions import Fraction
from calendar import isleap, monthrange
import json
from pathlib import Path

from bom_cdo_native_revision_audit import audit, read_set
from bom_panel_trend_sensitivity import analyze as analyze_annual_panel


def exact(d):
    return Fraction(str(d))


def fraction_text(x):
    return str(x.numerator) if x.denominator == 1 else f'{x.numerator}/{x.denominator}'


def conditional_month_delta_bounds(before_rows, after_rows, station, variable, month, low, high):
    """Sharp fixed-calendar change bounds under EXPLICIT daily-value bounds.

    Unknown observations may independently range over [low, high]. Known
    one-day observations are fixed. A multi-day accumulated record cannot
    identify a daily reading, so its day is unknown rather than imputed.
    No climate-instrument range is assumed by this function.
    """
    if variable not in ('tmax', 'tmin'):
        raise ValueError('temperature bounds cannot be applied to rainfall')
    low, high = exact(low), exact(high)
    if low > high:
        raise ValueError('temperature lower bound exceeds upper bound')
    yy, mm = map(int, month.split('-'))
    n = monthrange(yy, mm)[1]
    sum_lower = sum_upper = Fraction()
    unknown_before = unknown_after = 0
    for day_number in range(1, n + 1):
        day = f'{month}-{day_number:02d}'
        key = (station, day, variable)
        old, new = before_rows.get(key), after_rows.get(key)
        b = exact(old[0]) if old is not None and old[0] is not None and old[1] == 1 else None
        a = exact(new[0]) if new is not None and new[0] is not None and new[1] == 1 else None
        for known in (b, a):
            if known is not None and not (low <= known <= high):
                raise ValueError(f'observed daily value outside assumed range: {key}')
        if b is None:
            unknown_before += 1
        if a is None:
            unknown_after += 1
        sum_lower += (a if a is not None else low) - (b if b is not None else high)
        sum_upper += (a if a is not None else high) - (b if b is not None else low)
    return {
        'assumed_daily_min_C': fraction_text(low),
        'assumed_daily_max_C': fraction_text(high),
        'lower_fixed_calendar_delta_C': fraction_text(sum_lower / n),
        'upper_fixed_calendar_delta_C': fraction_text(sum_upper / n),
        'unknown_before_days': unknown_before,
        'unknown_after_days': unknown_after,
        'bounds_are_conditional_not_measured': True,
        'sharp_only_for_independent_in_range_unknown_daily_values': True,
    }


def conditional_annual_trend_bounds(months):
    """Lift complete calendar-year temperature intervals through exact OLS.

    Uses the same day-count weights and centred-year denominator as the
    existing bom_panel_trend_sensitivity owner; selects interval endpoints
    based on the signed regression leverage. No missing year is imputed.
    Conditional independent-box bounds only, NOT a national ACORN-SAT trend.
    """
    grouped = defaultdict(dict)
    for m in months:
        interval = m.get('conditional_fixed_calendar_delta_interval')
        if interval is None or m['variable'] not in ('tmax', 'tmin'):
            continue
        yy, mm = map(int, m['month'].split('-'))
        key = (m['station'], m['variable'], yy)
        if mm in grouped[key]:
            raise ValueError('duplicate month interval receipt')
        lower = Fraction(interval['lower_fixed_calendar_delta_C'])
        upper = Fraction(interval['upper_fixed_calendar_delta_C'])
        days = int(m['expected_calendar_days'])
        if lower > upper or days != monthrange(yy, mm)[1]:
            raise ValueError('invalid conditional month interval or calendar')
        grouped[key][mm] = (lower, upper, days)
    annual = []
    for (station, variable, year), months_by_number in sorted(grouped.items()):
        if set(months_by_number) != set(range(1, 13)):
            continue
        days = sum(d for lo, hi, d in months_by_number.values())
        if days != (366 if isleap(year) else 365):
            raise ValueError('inconsistent annual calendar')
        lower = sum((lo*d for lo, hi, d in months_by_number.values()), Fraction()) / days
        upper = sum((hi*d for lo, hi, d in months_by_number.values()), Fraction()) / days
        annual.append({
            'station': station, 'variable': variable, 'year': year, 'days': days,
            'lower_exact_C': fraction_text(lower),
            'upper_exact_C': fraction_text(upper),
            'conditional_not_measured': True,
        })
    station_years = defaultdict(list)
    for row in annual:
        station_years[(row['station'], row['variable'])].append(row)
    trends = []
    for (station, variable), rows in sorted(station_years.items()):
        if len(rows) < 2:
            continue
        weight_total = sum((Fraction(y['days']) for y in rows), Fraction())
        center = sum((Fraction(y['days'] * y['year']) for y in rows), Fraction()) / weight_total
        denominator = sum((Fraction(y['days']) * (y['year']-center)**2
                           for y in rows), Fraction())
        if denominator <= 0:
            raise ValueError('zero centred year variance')
        lower = upper = Fraction()
        for y in rows:
            leverage = Fraction(10*y['days']) * (y['year']-center) / denominator
            lo = Fraction(y['lower_exact_C'])
            hi = Fraction(y['upper_exact_C'])
            lower += leverage * (lo if leverage >= 0 else hi)
            upper += leverage * (hi if leverage >= 0 else lo)
        trends.append({
            'station': station, 'variable': variable, 'years': len(rows),
            'first_year': min(y['year'] for y in rows),
            'last_year': max(y['year'] for y in rows),
            'lower_exact_C_per_decade': fraction_text(lower),
            'upper_exact_C_per_decade': fraction_text(upper),
            'interval_conditional_not_measured': True,
            'selected_years_only_missing_years_not_imputed': True,
            'national_trend_authorised': False,
        })
    return annual, trends


def summarize(manifest, root, temperature_min=None, temperature_max=None):
    if (temperature_min is None) != (temperature_max is None):
        raise ValueError('supply both explicit temperature bounds or neither')
    if temperature_min is not None and exact(temperature_min) > exact(temperature_max):
        raise ValueError('temperature bounds reversed')
    ledger = audit(manifest, root)
    before, _ = read_set(manifest['before'], root)
    after, _ = read_set(manifest['after'], root)
    groups = defaultdict(set)
    for station, day, variable in set(before) | set(after):
        groups[(station, variable, day[:7])].add(day)
    months = []
    annual_groups = defaultdict(dict)
    for (station, variable, month), _ in sorted(groups.items()):
        yy, mm = map(int, month.split('-'))
        expected = monthrange(yy, mm)[1]
        missing_days = []
        missing_values = []
        accum_mismatch = []
        comparable = []
        changed = 0
        available_before, available_after = [], []
        quality_before, quality_after = defaultdict(int), defaultdict(int)
        for d in range(1, expected + 1):
            day = f'{month}-{d:02d}'
            key = (station, day, variable)
            b, a = before.get(key), after.get(key)
            # Available-case statistics have their OWN denominator. A blanked
            # day is not imputed, and a missing later row is not a verified
            # physical deletion from the original instrument book.
            if b is not None:
                quality_before[b[2] or '<blank>'] += 1
                if b[0] is not None and b[1] == 1:
                    available_before.append(exact(b[0]))
            if a is not None:
                quality_after[a[2] or '<blank>'] += 1
                if a[0] is not None and a[1] == 1:
                    available_after.append(exact(a[0]))
            if b is None or a is None:
                missing_days.append(day)
            elif b[0] is None or a[0] is None:
                missing_values.append(day)
            elif b[1] != 1 or a[1] != 1:
                accum_mismatch.append(day)
            else:
                bv, av = exact(b[0]), exact(a[0])
                comparable.append((bv, av))
                changed += int(bv != av)
        complete = not (missing_days or missing_values or accum_mismatch)
        record = {
            'station': station, 'variable': variable, 'month': month,
            'expected_calendar_days': expected,
            'paired_numeric_one_day_values': len(comparable),
            'changed_paired_daily_values': changed,
            'missing_calendar_days': len(missing_days),
            'missing_numeric_values': len(missing_values),
            'multi_day_or_unknown_accumulations': len(accum_mismatch),
            'complete_same_day_month': complete,
            'true_original_observation_verified': False,
            'before_available_numeric_days': len(available_before),
            'after_available_numeric_days': len(available_after),
            'before_quality_flag_counts': dict(sorted(quality_before.items())),
            'after_quality_flag_counts': dict(sorted(quality_after.items())),
        }
        if comparable:
            pairdelta = sum((a - b for b, a in comparable), Fraction())
            record['paired_day_delta_sum_exact'] = fraction_text(pairdelta)
            record['paired_day_delta_average_exact'] = fraction_text(pairdelta/len(comparable))
            record['paired_day_summary_is_full_month'] = complete
        # Incomplete publications may still have an observed-only mean.
        # It answers a question about *available reported readings*, not
        # the fixed-calendar climate statistic or a paper-ledger correction.
        if variable in ('tmax', 'tmin'):
            if available_before:
                mean_before = sum(available_before, Fraction()) / len(available_before)
                record['available_case_before_mean_exact'] = fraction_text(mean_before)
            if available_after:
                mean_after = sum(available_after, Fraction()) / len(available_after)
                record['available_case_after_mean_exact'] = fraction_text(mean_after)
            if available_before and available_after:
                delta = mean_after - mean_before
                record['available_case_mean_change_exact'] = fraction_text(delta)
                record['available_case_mean_denominator_changed'] = len(available_before) != len(available_after)
                record['available_case_is_fixed_calendar_climate_mean'] = complete
                if comparable:
                    shared_b = sum((b for b, _ in comparable), Fraction()) / len(comparable)
                    shared_a = sum((a for _, a in comparable), Fraction()) / len(comparable)
                    within = shared_a - shared_b
                    composition = delta - within
                    assert within + composition == delta
                    record['common_support_mean_change_exact'] = fraction_text(within)
                    record['composition_change_exact'] = fraction_text(composition)
                    record['composition_includes_missingness_or_unpaired_days'] = not complete
        else:
            record['available_case_before_rain_subtotal_exact'] = fraction_text(
                sum(available_before, Fraction()))
            record['available_case_after_rain_subtotal_exact'] = fraction_text(
                sum(available_after, Fraction()))
            record['available_case_subtotals_are_full_month'] = complete
        if complete:
            assert len(comparable) == expected
            total_before = sum((b for b, _ in comparable), Fraction())
            total_after = sum((a for _, a in comparable), Fraction())
            divisor = expected if variable != 'rain' else 1
            record['full_month_before_exact'] = fraction_text(total_before / divisor)
            record['full_month_after_exact'] = fraction_text(total_after / divisor)
            record['full_month_delta_exact'] = fraction_text((total_after-total_before)/divisor)
            record['statistic'] = ('daily-mean temperature C' if variable != 'rain'
                                   else 'total rainfall mm')
            annual_groups[(station, variable, yy)][mm] = (total_before, total_after, expected)
        else:
            record['full_month_delta_exact'] = None
            record['statistic'] = 'UNRESOLVED: full-month quantity unavailable'
        if variable in ('tmax', 'tmin') and temperature_min is not None:
            record['conditional_fixed_calendar_delta_interval'] = conditional_month_delta_bounds(
                before, after, station, variable, month,
                temperature_min, temperature_max)
        months.append(record)
    conditional_annual, conditional_trends = conditional_annual_trend_bounds(months)
    years = []
    for (station, variable, year), monthly in sorted(annual_groups.items()):
        if set(monthly) != set(range(1, 13)):
            continue
        before_total = sum((b for b, _, _ in monthly.values()), Fraction())
        after_total = sum((a for _, a, _ in monthly.values()), Fraction())
        days = sum(d for _, _, d in monthly.values())
        assert days in (365, 366)
        divisor = days if variable != 'rain' else 1
        years.append({
            'station': station, 'variable': variable, 'year': year,
            'before_exact': fraction_text(before_total / divisor),
            'after_exact': fraction_text(after_total / divisor),
            'delta_exact': fraction_text((after_total-before_total)/divisor),
            'statistic': ('daily-mean temperature C' if variable != 'rain'
                          else 'total rainfall mm'),
            'complete_same_day_annual_panel': True,
        })
    trend_panels = defaultdict(list)
    for annual in years:
        if annual['variable'] in ('tmax', 'tmin'):
            yy = annual['year']
            weight = Fraction(366 if isleap(yy) else 365)
            trend_panels[(annual['station'], annual['variable'])].append(
                (yy, weight, Fraction(annual['before_exact']),
                 Fraction(annual['after_exact'])))
    station_trends = []
    for (station, variable), data in sorted(trend_panels.items()):
        if len(data) < 2:
            continue
        result = analyze_annual_panel(sorted(data))
        station_trends.append({
            'station': station, 'variable': variable,
            'scope': 'complete native station-years only; not ACORN-SAT',
            'annual_panel': result,
        })
    return {
        'schema': 'dashi.bom.cdo.paired_publication_impact.v1',
        'source_receipts': {'before': ledger['before_receipts'],
                            'after': ledger['after_receipts']},
        'status': 'publication-version comparison; not original-correction or national trend',
        'original_archive_coverage_verified': False,
        'paper_original_authenticated': False,
        'acorn_homogenisation_recomputed': False,
        'counts': {
            'months_seen': len(months),
            'complete_months': sum(x['complete_same_day_month'] for x in months),
            'incomplete_months': sum(not x['complete_same_day_month'] for x in months),
            'complete_station_years': len(years),
        },
        'months': months, 'years': years, 'station_trends': station_trends,
        'conditional_complete_calendar_station_year_intervals': conditional_annual,
        'conditional_selected_year_station_trend_intervals': conditional_trends,
        'native_revision_counts': ledger['counts'],
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manifest', type=Path, required=True)
    p.add_argument('--temperature-min', help='Optional ASSUMED daily lower C limit')
    p.add_argument('--temperature-max', help='Optional ASSUMED daily upper C limit')
    p.add_argument('--output', type=Path)
    a = p.parse_args()
    manifest = json.loads(a.manifest.read_text(encoding='utf-8'))
    result = summarize(manifest, a.manifest.parent, a.temperature_min, a.temperature_max)
    data = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if a.output:
        a.output.write_text(data, encoding='utf-8')
    else:
        print(data, end='')


if __name__ == '__main__':
    main()
