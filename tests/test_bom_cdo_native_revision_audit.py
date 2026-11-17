"""Original BOM native CSV regression suite. Inputs synthetic; no Lloyd claim verified."""
from hashlib import sha256
import importlib.util
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('native',ROOT/'scripts/bom_cdo_native_revision_audit.py')
native=importlib.util.module_from_spec(spec)
spec.loader.exec_module(native)
HEADER=('Product code,Bureau of Meteorology station number,Year,Month,Day,'
        'Maximum temperature (Degree C),Days of accumulation of maximum temperature,Quality\n')

def fixture(root,before,after):
    result={'schema':'dashi.bom.cdo.native_revision.v1'}
    for name,data in [('before',before),('after',after)]:
        raw=(HEADER+data).encode('utf8')
        (root/(name+'.csv')).write_bytes(raw)
        result[name]=[{'path':name+'.csv','sha256':sha256(raw).hexdigest(),
                       'capture_utc':'2026-05-19T09:00:00+10:00' if name=='before'
                                    else '2026-10-30T09:00:00+10:00'}]
    return result

def line(station='66062',year=1907,month=8,day=1,value='16.2',accum='1',flag='Y'):
    return f'IDCJAC0010,{station},{year},{month},{day},{value},{accum},{flag}\n'

class NativeTest(unittest.TestCase):
    def run_native(self,old,new):
        with TemporaryDirectory() as tmp:
            root=Path(tmp)
            return native.audit(fixture(root,old,new),root)
    def test_removed(self):
        r=self.run_native(line(),line(value=''))
        self.assertEqual(r['counts'],{'value_removed':1})
        self.assertEqual(r['before2025_observed_values_lost_by_station'],{'066062':1})
        self.assertFalse(r['before2025_target_numeric_match_only'])
    def test_quality_change(self):
        self.assertEqual(self.run_native(line(),line(flag='N'))['counts'],{'quality_flag_changed':1})
    def test_station_not_interchangeable(self):
        with TemporaryDirectory() as tmp:
            root=Path(tmp)
            m=fixture(root,line(),line(station='44022'))
            with self.assertRaises(native.AuditError):native.audit(m,root)
    def test_changed_value(self):
        self.assertEqual(self.run_native(line(),line(value='18.2'))['counts'],{'value_changed':1})
    def test_zero_events_not_571(self):
        r=self.run_native(line(),line())
        self.assertEqual(r['counts'],{})
        self.assertFalse(r['before2025_target_numeric_match_only'])
    def test_numeric_format(self):
        self.assertEqual(self.run_native(line(),line(value='16.20'))['counts'],{})
    def test_bad_hash(self):
        with TemporaryDirectory() as tmp:
            root=Path(tmp);m=fixture(root,line(),line())
            (root/'before.csv').write_text('tampered')
            with self.assertRaises(native.AuditError):native.audit(m,root)
    def test_duplicate_key(self):
        with self.assertRaises(native.AuditError):self.run_native(line()+line(),line())
    def test_missing_row_separate_from_missing_value(self):
        r=self.run_native(line()+line(day=2),line())
        self.assertEqual(r['counts'],{'calendar_row_removed':1})
    def test_reversed_capture_time(self):
        with TemporaryDirectory() as tmp:
            root=Path(tmp);m=fixture(root,line(),line())
            m['before'][0]['capture_utc']='2026-11-01T09:00:00+10:00'
            with self.assertRaises(native.AuditError):native.audit(m,root)
    def test_both_maximum_and_minimum_losses_count_for_same_station(self):
        with TemporaryDirectory() as tmp:
            root=Path(tmp)
            manifest={'schema':'dashi.bom.cdo.native_revision.v1','before':[],'after':[]}
            for label, date_day, product in (('Maximum',1,'IDCJAC0010'),('Minimum',2,'IDCJAC0011')):
                h=(f'Product code,Bureau of Meteorology station number,Year,Month,Day,'
                   f'{label} temperature (Degree C),Days of accumulation of {label.lower()} temperature,Quality\n')
                for snapshot in ('before','after'):
                    name=f'{snapshot}_{product}.csv'
                    csv_data=(h+f'{product},066062,1905,01,{date_day},'
                              + ('20.1' if snapshot=='before' else '')+',1,Y\n').encode()
                    (root/name).write_bytes(csv_data)
                    manifest[snapshot].append({'path':name,
                      'sha256':sha256(csv_data).hexdigest(),
                      'capture_utc':('2026-05-19T09:00:00+10:00' if snapshot=='before'
                                     else '2026-10-30T09:00:00+10:00')})
            out=native.audit(manifest,root)
            self.assertEqual(out['before2025_observed_values_lost_by_station'],{'066062':2})
            self.assertEqual(out['before2025_observed_values_lost_by_station_product'],
                             {'066062:tmax':1,'066062:tmin':1})
    def test_blank_accumulation_is_one_day_for_present_temperature(self):
        self.assertEqual(self.run_native(line(accum=''),line(accum='1'))['counts'],{})

    def test_missing_value_with_blank_accumulation_stays_missing(self):
        self.assertEqual(self.run_native(line(value='',accum=''),line(value='',accum=''))['counts'],{})

    def test_simultaneous_removed_value_and_quality_change(self):
        out=self.run_native(line(),line(value='',flag='N'))
        self.assertEqual(out['counts'],{'value_removed':1})
        self.assertEqual(out['field_change_counts'],
                         {'observed_value':1,'quality_flag':1})
        self.assertEqual(out['events'][0]['changed_fields'],
                         ['observed_value','quality_flag'])

    def test_historical_includes_2000_through_2024(self):
        old='IDCJAC0010,66062,2024,12,31,23.2,1,Y\n'
        new='IDCJAC0010,66062,2024,12,31,,1,Y\n'
        result=self.run_native(old,new)
        self.assertEqual(result['before2025_observed_values_lost_by_station'],{'066062':1})

    def test_recent_2025_excluded_from_historical(self):
        old='IDCJAC0010,66062,2025,01,01,23.2,1,Y\n'
        new='IDCJAC0010,66062,2025,01,01,,1,Y\n'
        result=self.run_native(old,new)
        self.assertEqual(result['before2025_observed_values_lost_by_station'],{})

    def test_accumulation_change(self):
        self.assertEqual(self.run_native(line(),line(accum='2'))['counts'],{'accumulation_changed':1})

if __name__=='__main__':unittest.main()
