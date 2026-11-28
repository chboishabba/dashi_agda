"""Exact portable geometry checks, not actual mmgroup execution."""
import unittest
import numpy as np
from scripts.check_x369_concrete_leech_golay_glue import golay
from scripts.x369_actual_leech_coordinate_alignment import permutation,permute_mask
from scripts.x369_actual_3b_normalizer_tensor import monomial,fixed_line,WEIGHTS,ZERO


class ActualGeometryContracts(unittest.TestCase):
    def test_golay_octad_coordinate_extension(self):
        src=golay()
        p=tuple((5*i+7)%24 for i in range(24))
        tgt={permute_mask(x,p) for x in src}
        q,rounds=permutation(src,tgt)
        self.assertEqual({permute_mask(x,q) for x in src},tgt)
        self.assertEqual(sum(r['new_points'] for r in rounds),17)

    def test_reference_weyl_phase_and_fixed_line(self):
        e=tuple(int(i==0) for i in range(6))
        for z in (2,4):
            v=np.arange(729,dtype=np.int64)%7
            a=(e,ZERO,0);b=(ZERO,e,0)
            # Right action: v*B*A = z * v*A*B.
            self.assertTrue(np.array_equal(monomial(monomial(v,b,z),a,z),
                              z*monomial(monomial(v,a,z),b,z)%7))
            mods=[(ZERO,tuple(int(i==j) for i in range(6)),0) for j in range(6)]
            u,w=fixed_line(mods,z)
            self.assertEqual(u,ZERO)
            self.assertEqual(np.count_nonzero(w),1)
            self.assertEqual(w[0],1)
            # Pure Fourier-polarization swap: fixed translations yield
            # the constant vector, not a single weight.
            trans=[(tuple(int(i==j) for i in range(6)),ZERO,0) for j in range(6)]
            u,w=fixed_line(trans,z)
            self.assertEqual(u,ZERO)
            self.assertTrue(np.all(w==1))


if __name__=='__main__':unittest.main()
