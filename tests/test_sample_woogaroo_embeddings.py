import csv
import sys
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from sample_woogaroo_embeddings import read_sampling_locations,assemble

class TestSample(unittest.TestCase):
    def test_local_join(self):
        with TemporaryDirectory() as directory:
            path=Path(directory)/'labels.csv'
            with path.open('w',newline='') as handle:
                writer=csv.DictWriter(handle,fieldnames=['lon','lat','year','label','label_source','baseline_elevation'])
                writer.writeheader()
                writer.writerows([{'lon':'152.9','lat':'-27.7','year':'2022','label':'1.3','label_source':'survey-1','baseline_elevation':'33'},
                                  {'lon':'152.91','lat':'-27.7','year':'2024','label':'2.6','label_source':'survey-2','baseline_elevation':'35'}])
            rows,features=read_sampling_locations(path)
            self.assertEqual(features,['baseline_elevation'])
            self.assertNotEqual(rows[0]['cell'],rows[1]['cell'])
            data=assemble(rows,np.ones((2,64)),np.ones((2,128)))
            self.assertEqual(data['alpha'].shape,(2,64))
            self.assertEqual(data['baseline'].shape,(2,1))
    def test_reject_same_cell_year(self):
        with TemporaryDirectory() as directory:
            path=Path(directory)/'labels.csv'
            path.write_text('lon,lat,year,label,label_source,baseline_x\n152.9,-27.7,2022,1,a,2\n152.9,-27.7,2022,3,b,4\n')
            with self.assertRaisesRegex(ValueError,'duplicate'):
                read_sampling_locations(path)

if __name__=='__main__':unittest.main()
