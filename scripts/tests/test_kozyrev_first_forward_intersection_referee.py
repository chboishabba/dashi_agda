import math
import unittest
from kozyrev_first_forward_intersection_referee import surfaces,first_cross
class FirstForward(unittest.TestCase):
    def test_first_ray_intersection(self):
        g=dict(inner=1.5,growth=.1,turns=1.5,thick=.1,srot=0,family="arch")
        a=surfaces(g,10000)
        hit=first_cross(a,(-3.,0.),(1.,0.))
        self.assertTrue(math.isfinite(hit))
        self.assertGreater(hit,0)
    def test_no_hit_behind(self):
        g=dict(inner=1.5,growth=.1,turns=1.5,thick=.1,srot=0,family="arch")
        self.assertTrue(math.isinf(first_cross(surfaces(g,4000),(10,10),(1.,0.))))
    def test_shape_sampling_converges(self):
        g=dict(inner=1.5,growth=.1,turns=1.5,thick=.1,srot=0,family="arch")
        a=first_cross(surfaces(g,10000),(-3,0),(1.,0.))
        b=first_cross(surfaces(g,20000),(-3,0),(1.,0.))
        self.assertLess(abs(a-b),.0001)
if __name__=="__main__":unittest.main()
