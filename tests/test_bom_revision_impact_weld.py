"""Finite synthetic publication-mean and missingness acceptance tests."""
import calendar
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import bom_revision_impact_weld as weld

HEADER=('Product code,Bureau of Meteorology station number,Year,Month,Day,'
        'Maximum temperature (Degree C),Days of accumulation of maximum temperature,Quality\n')
RAINHEADER=('Product code,Bureau of Meteorology station number,Year,Month,Day,'
        'Rainfall amount (millimetres),Period over which rainfall was measured (days),Quality\n')


def month_rows(year,month,variable='tmax',value='10.0'):
    product='IDCJAC0010' if variable=='tmax' else 'IDCJAC0009'
    header=HEADER if variable=='tmax' else RAINHEADER
    return header+''.join(f'{product},066062,{year},{month},{i},{value},1,Y\n'
                          for i in range(1,calendar.monthrange(year,month)[1]+1))


def replace_day(text,year,month,day,value,accum=None):
    lines=text.splitlines()
    for i,s in enumerate(lines[1:],1):
        parts=s.split(',')
        if tuple(map(int,parts[2:5]))==(year,month,day):
            parts[5]=value
            if accum is not None: parts[6]=str(accum)
            lines[i]=','.join(parts)
            return '\n'.join(lines)+'\n'
    raise AssertionError('missing')


class WeldTest(unittest.TestCase):
    def run_pair(self,old,new):
        with TemporaryDirectory() as tmp:
            root=Path(tmp)
            manifest={'schema':'dashi.bom.cdo.native_revision.v1'}
            for side,content in (('before',old),('after',new)):
                path=f'{side}.csv';buf=content.encode()
                (root/path).write_bytes(buf)
                manifest[side]=[{'path':path,'sha256':sha256(buf).hexdigest(),
                    'capture_utc':'2026-05-01T10:00:00+10:00' if side=='before'
                    else '2026-10-30T10:00:00+10:00'}]
            return weld.summarize(manifest,root)

    def test_deletion_changes_available_case_mean_not_fixed_calendar_mean(self):
        before=replace_day(month_rows(1910,2),1910,2,1,'20')
        after=replace_day(before,1910,2,1,'')
        m=self.run_pair(before,after)['months'][0]
        self.assertIsNone(m['full_month_delta_exact'])
        self.assertEqual((m['before_available_numeric_days'],m['after_available_numeric_days']),(28,27))
        self.assertEqual(m['available_case_before_mean_exact'],'145/14')
        self.assertEqual(m['available_case_after_mean_exact'],'10')
        self.assertEqual(m['available_case_mean_change_exact'],'-5/14')
        self.assertEqual(m['common_support_mean_change_exact'],'0')
        self.assertEqual(m['composition_change_exact'],'-5/14')
        self.assertTrue(m['available_case_mean_denominator_changed'])
        self.assertFalse(m['available_case_is_fixed_calendar_climate_mean'])

    def test_composition_decomposes_with_simultaneous_shared_day_change(self):
        from fractions import Fraction
        before=replace_day(month_rows(1910,2),1910,2,1,'20')
        after=replace_day(before,1910,2,1,'')
        after=replace_day(after,1910,2,2,'17')
        m=self.run_pair(before,after)['months'][0]
        total=Fraction(m['available_case_mean_change_exact'])
        within=Fraction(m['common_support_mean_change_exact'])
        composition=Fraction(m['composition_change_exact'])
        self.assertEqual(within, Fraction(7,27))
        self.assertEqual(total,within+composition)
        self.assertIsNone(m['full_month_delta_exact'])

    def test_rainfall_missing_day_retains_only_observed_subtotals(self):
        before=month_rows(1910,2,'rain','2')
        after=replace_day(before,1910,2,1,'')
        m=self.run_pair(before,after)['months'][0]
        self.assertEqual(m['available_case_before_rain_subtotal_exact'],'56')
        self.assertEqual(m['available_case_after_rain_subtotal_exact'],'54')
        self.assertFalse(m['available_case_subtotals_are_full_month'])
        self.assertIsNone(m['full_month_delta_exact'])

    def test_quality_flags_reported_without_claim_of_accuracy(self):
        before=month_rows(1910,2)
        after=before.replace(',1,Y\n',',1,N\n',1)
        m=self.run_pair(before,after)['months'][0]
        self.assertEqual(m['before_quality_flag_counts'],{'Y':28})
        self.assertEqual(m['after_quality_flag_counts'],{'N':1,'Y':27})
        self.assertTrue(m['complete_same_day_month'])
        self.assertFalse(m['true_original_observation_verified'])

    def test_complete_month_changed_one_day_mean(self):
        a=month_rows(1910,2)
        b=replace_day(a,1910,2,1,'17.0')
        m=self.run_pair(a,b)['months'][0]
        self.assertTrue(m['complete_same_day_month'])
        self.assertEqual(m['full_month_delta_exact'],'1/4')
        self.assertEqual(m['changed_paired_daily_values'],1)
        self.assertEqual(m['paired_day_delta_sum_exact'],'7')

    def test_removed_value_is_not_imputed(self):
        a=month_rows(1910,2);b=replace_day(a,1910,2,1,'')
        m=self.run_pair(a,b)['months'][0]
        self.assertFalse(m['complete_same_day_month'])
        self.assertIsNone(m['full_month_delta_exact'])
        self.assertEqual(m['missing_numeric_values'],1)

    def test_missing_row_is_not_imputed(self):
        a=month_rows(1910,2)
        b='\n'.join(x for x in a.splitlines() if ',1910,2,1,' not in x)+'\n'
        m=self.run_pair(a,b)['months'][0]
        self.assertFalse(m['complete_same_day_month'])
        self.assertEqual(m['missing_calendar_days'],1)
        self.assertIsNone(m['full_month_delta_exact'])

    def test_multi_day_rainfall_not_daily_sum(self):
        a=month_rows(1910,2,'rain','2')
        b=replace_day(a,1910,2,1,'3',accum=3)
        m=self.run_pair(a,b)['months'][0]
        self.assertFalse(m['complete_same_day_month'])
        self.assertEqual(m['multi_day_or_unknown_accumulations'],1)

    def test_complete_rainfall_total(self):
        a=month_rows(1910,2,'rain','2')
        b=replace_day(a,1910,2,1,'3')
        m=self.run_pair(a,b)['months'][0]
        self.assertEqual(m['full_month_delta_exact'],'1')
        self.assertEqual(m['statistic'],'total rainfall mm')

    def test_incomplete_calendar_does_not_extrapolate(self):
        a=month_rows(1910,2);b=replace_day(a,1910,2,1,'17')
        for d in (27,28):
            a='\n'.join(x for x in a.splitlines() if f',1910,2,{d},' not in x)+'\n'
            b='\n'.join(x for x in b.splitlines() if f',1910,2,{d},' not in x)+'\n'
        m=self.run_pair(a,b)['months'][0]
        self.assertFalse(m['complete_same_day_month'])
        self.assertEqual(m['paired_numeric_one_day_values'],26)
        self.assertIsNone(m['full_month_delta_exact'])

    def test_same_numeric_format(self):
        a=month_rows(1910,2);b=replace_day(a,1910,2,1,'10.00')
        m=self.run_pair(a,b)['months'][0]
        self.assertEqual(m['changed_paired_daily_values'],0)
        self.assertEqual(m['full_month_delta_exact'],'0')

    def test_no_claim_about_causation(self):
        a=month_rows(1910,2);out=self.run_pair(a,a)
        self.assertFalse(out['original_archive_coverage_verified'])
        self.assertFalse(out['paper_original_authenticated'])
        self.assertFalse(out['acorn_homogenisation_recomputed'])
        self.assertEqual(out['counts']['complete_station_years'],0)

    def test_station_trend_reuses_exact_panel_owner(self):
        a=HEADER+''.join(month_rows(y,m).split('\n',1)[1]
                         for y in (1910,1911) for m in range(1,13))
        b=replace_day(a,1910,2,1,'17')
        result=self.run_pair(a,b)
        self.assertEqual(result['counts']['complete_station_years'],2)
        self.assertEqual(len(result['station_trends']),1)
        panel=result['station_trends'][0]['annual_panel']
        self.assertEqual(panel['exact_difference_C_per_decade'],'-14/73')
        self.assertFalse(panel['national_trend_claim_authorised'])

    def test_complete_station_year_weighted_by_days(self):
        a=HEADER+''.join(month_rows(1910,m).split('\n',1)[1] for m in range(1,13))
        b=replace_day(a,1910,2,1,'17')
        out=self.run_pair(a,b)
        self.assertEqual(out['counts']['complete_station_years'],1)
        self.assertEqual(out['years'][0]['delta_exact'],'7/365')


if __name__=='__main__':
    unittest.main()
