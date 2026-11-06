import math
import unittest
from kozyrev_matched_envelope_html import normalized_geometry
class Envelope(unittest.TestCase):
    def test_matched_endpoints(self):
        for family in ("arch","log","segmented"):
            s={"geometry":{"inner":1.5,"growth":.402,"turns":1.5}}
            g=normalized_geometry(s,family,1.5,5.288760740229291)["geometry"]
            t=2*math.pi*g["turns"]
            outer=(g["inner"]*math.exp(g["growth"]*t) if family=="log" else
                   g["inner"]+g["growth"]*t+g["correction"]*math.sin(t/g["turns"]))
            self.assertAlmostEqual(outer,5.288760740229291)
if __name__=="__main__":unittest.main()
