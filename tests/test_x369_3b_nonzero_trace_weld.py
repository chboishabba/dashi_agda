import unittest
from fractions import Fraction as F
from scripts.x369_3b_nonzero_weyl_trace import nonzero_trace,WEIGHTS,Z,mul_coord,inv_coord
from scripts.x369_3b_cyclotomic_rank import Q,ONE,ZERO
from scripts.x369_3b_source_trace_character_weld import phase_trace,qcyc


class NonzeroTrace(unittest.TestCase):
    def test_identity_and_translation_and_modulation(self):
        e=[tuple(int(i==j) for i in range(6)) for j in range(6)]
        for p in (1,2):
            aa=[(a,Z,0) for a in e]
            phi=[ZERO]*729;phi[0]=ONE
            w,t,o,_=nonzero_trace(phi,aa,p)
            self.assertEqual(w,(Z,Z,0));self.assertEqual(t,Q(F(729)));self.assertEqual(o,t)
            r=tuple(-x%3 for x in e[0]);phi=[ZERO]*729;phi[WEIGHTS.index(r)]=ONE
            w,t,o,_=nonzero_trace(phi,aa,p)
            self.assertEqual(w,(r,Z,0));self.assertEqual(t,Q(F(729)));self.assertEqual(o,ZERO)
            phi=[ZERO]*729;phi[0]=ONE
            aa=[(a,Z,(-int(i==0))%3) for i,a in enumerate(e)]
            w,t,o,_=nonzero_trace(phi,aa,p)
            self.assertEqual(w,(Z,r,0));self.assertEqual(t,Q(F(729)));self.assertEqual(o,ZERO)
            self.assertEqual(mul_coord(w,inv_coord(w)),(Z,Z,0))

    def test_phase_trace_from_actual_character_formula(self):
        # Identity and central 3B shifts, published dimensions only.
        vals=[qcyc(Q(F(196884))),qcyc(Q(F(54))),qcyc(Q(F(54)))]
        for p in (1,2):self.assertEqual(phase_trace(vals,p),65610)
        vals=[qcyc(Q(F(1458))),qcyc(Q(F(-729))),qcyc(Q(F(-729)))]
        for p in (1,2):self.assertEqual(phase_trace(vals,p),729)

if __name__=='__main__':unittest.main()
