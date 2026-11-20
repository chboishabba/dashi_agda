"""Native small-grid affine stage parity using the original compact TT cell producer."""
import unittest
import numpy as np
from ksw668_f8_tt_multipole import stage,affine_mode3_stage
from ksw668_f8_fv_source_flux import exact_cell_averages

class NativeAffineStage(unittest.TestCase):
    def test_native_compact_source(self):
        rng=np.random.default_rng(102)
        nr=17; dr=.008; dy=.02
        src=exact_cell_averages(.04,np.arange(nr)*dr,dr)
        cp=np.zeros_like(src);cm=np.zeros_like(src)
        for q in range(3):
            d=3+4*q
            for j in range(1,nr):
                den=(j+.5)**d-(j-.5)**d
                cp[q,j]=d*(j+.5)**(d-1)/den
                cm[q,j]=d*(j-.5)**(d-1)/den
        for ny in (8,17,31):
            for v in (-.7,-.6,-.09):
                for amp in (0.,.7):
                    U,P,M=rng.normal(size=(3,3,ny,nr))
                    for x in (U,P,M):x[:,:,-1]=0
                    a=[np.empty_like(U) for _ in range(3)]
                    b=[np.empty_like(U) for _ in range(3)]
                    args=(dr,dy,.75,v,amp,src,cp,cm,3)
                    stage(U,P,M,*a,*args)
                    affine_mode3_stage(stage,U,P,M,*b,*args)
                    for x,y in zip(a,b):
                        np.testing.assert_allclose(x,y,atol=1e-8,rtol=1e-11)
if __name__=='__main__':unittest.main()
