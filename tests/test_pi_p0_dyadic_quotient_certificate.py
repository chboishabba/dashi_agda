"""Exact integer equivalence tests for Paper 9 COMP5i/j certificate scheduling."""
import unittest

class DyadicCertificate(unittest.TestCase):
    def test_exact_quotient_and_strict_upper(self):
        checks=0
        for n in range(257):
            for bits in range(9):
                for den in (1,2,3,5,11,37):
                    self.assertEqual(n//(den<<bits),(n>>bits)//den)
                    for x in (0,1,7,31):
                        self.assertEqual(n<((x+1)*den<<bits),
                                         (n>>bits)<((x+1)*den))
                    checks+=1
        self.assertEqual(checks,13878)

    def test_power5_denominator_cancellation(self):
        checks=0
        for digits in (0,1,2,3,5,9):
            for bits in (digits,digits+1,digits+17):
                for root in (1,2,17,101):
                    for series_num,series_den in ((1,1),(19,23),(7,11)):
                        plain=426880*root*(10**digits)*series_den
                        compact=426880*root*(5**digits)*series_den
                        self.assertEqual(plain//(series_num<<bits),
                                         compact//(series_num<<(bits-digits)))
                        for x in (0,1,9):
                            self.assertEqual(plain<(x+1)*(series_num<<bits),
                                             (compact>>(bits-digits))<(x+1)*series_num)
                        checks+=1
        self.assertEqual(checks,216)

if __name__=="__main__":
    unittest.main()
