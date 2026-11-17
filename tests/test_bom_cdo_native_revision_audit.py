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
        self.assertEqual(r['pre2000_observed_values_lost_by_station'],{'066062':1})
        self.assertFalse(r['pre2000_target_matched'])
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
        self.assertFalse(r['pre2000_target_matched'])
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
    def test_accumulation_change(self):
        self.assertEqual(self.run_native(line(),line(accum='2'))['counts'],{'accumulation_changed':1})

if __name__=='__main__':unittest.main()
