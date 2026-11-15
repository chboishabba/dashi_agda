"""C3/Eisenstein three-flavour source-root reuse regression.

Distinct provenance:
- Finite roots/norm/cube geometry: DASHI.RelationalTernaryPhaseGeometry,
  DASHI.C3CyclotomicAmplitudeAlgebraExact, C3CubeCyclotomicFourierExact.
- Classical character orthogonality: Terras (1999), Serre (1977).
- Flavour-model prior art: Altarelli & Feruglio (2005, 2006, 2010);
  Grimus (2013); not an original DASHI physics prediction.
- Reactor parameter: NuFIT 6.1 (2025) sin²(theta13)≈0.0225.
- Finite C3 three-flavour reassembly here: new source-written
  mathematical model, NOT fitted PMNS or experimental likelihood.

All calculations use exact integers and fractions.  C3 phase zero
(label phase0) means the identity wave 1, not additive amplitude 0.
"""
from fractions import Fraction
from itertools import product
import unittest

# Integer pair a+b*zeta with zeta^2 = -1-zeta.
ONE = (1, 0)
ZETA = (0, 1)
ZETA2 = (-1, -1)
ZERO = (0, 0)
ROOTS = (ONE, ZETA, ZETA2)
M = ((1, 2, 2), (2, 1, -2), (2, -2, 1))


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def multiply(x, y):
    a, b = x
    c, d = y
    return a*c-b*d, a*d+b*c-b*d


def scale(n, x):
    return n*x[0], n*x[1]


def conjugate(x):
    a, b = x
    return a-b, -b


def norm(x):
    a, b = x
    return a*a-a*b+b*b


def amp_num(alpha, beta, phases):
    z = ZERO
    for i in range(3):
        z = add(z, scale(M[alpha][i]*M[beta][i], phases[i]))
    return z


def born_num(alpha, beta, phases):
    return norm(amp_num(alpha, beta, phases))


def f3_entry(row, col):
    return ROOTS[(row*col) % 3]


class C3NeutrinoBridgeTests(unittest.TestCase):
    def test_phase_roots_and_cancellation_are_different_from_zero_phase(self):
        self.assertEqual(add(add(ONE, ZETA), ZETA2), ZERO)
        self.assertEqual(multiply(ZETA, ZETA), ZETA2)
        self.assertEqual(multiply(ZETA, ZETA2), ONE)
        self.assertEqual(conjugate(ZETA), ZETA2)
        self.assertEqual([norm(p) for p in ROOTS], [1, 1, 1])
        self.assertEqual(norm(ZERO), 0)
        self.assertNotIn(ZERO, ROOTS)

    def test_exact_three_flavour_conservation_all_81_cases(self):
        for source, phases in product(range(3), product(ROOTS, repeat=3)):
            self.assertEqual(
                sum(born_num(source, detected, phases) for detected in range(3)),
                81
            )

    def test_c3_character_triplet_has_real_interference(self):
        self.assertEqual(
            [born_num(0, detected, ROOTS) for detected in range(3)],
            [9, 36, 36]
        )
        reverse = (ONE, ZETA2, ZETA)
        self.assertEqual(
            [born_num(0, detected, reverse) for detected in range(3)],
            [9, 36, 36]
        )
        self.assertEqual(sum((9, 36, 36)), 81)

    def test_reuses_exact_fourier_character_orthogonality(self):
        for row, other in product(range(3), repeat=2):
            s = ZERO
            for col in range(3):
                s = add(s, multiply(f3_entry(row, col),
                                    conjugate(f3_entry(other, col))))
            self.assertEqual(s, (3 if row == other else 0, 0))

    def test_c3_powers_have_order_three(self):
        for root in ROOTS:
            self.assertEqual(multiply(root, multiply(root, root)), ONE)

    def test_flat_fourier_not_physical_pmns(self):
        # U_3=F_3/sqrt(3) gives |U_e3|²=1/3, while M/3 has 4/9.
        # NuFIT's reactor value is around 0.0225, not either prediction.
        f3_s13_squared = Fraction(norm(f3_entry(0, 2)), 3)
        m_s13_squared = Fraction(M[0][2]**2, 9)
        loose_empirical_screen = Fraction(3, 100)
        self.assertEqual(f3_s13_squared, Fraction(1, 3))
        self.assertEqual(m_s13_squared, Fraction(4, 9))
        self.assertGreater(f3_s13_squared, loose_empirical_screen)
        self.assertGreater(m_s13_squared, loose_empirical_screen)

    def test_same_c3_scalar_carrier_does_not_select_unique_mixer(self):
        # Identity, rational orthogonal mixer and F3 all coexist with
        # the very same roots-of-unity carrier and have different reactor
        # amplitudes, so no C3 -> physical PMNS first-principles theorem.
        self.assertEqual(
            {Fraction(0, 1), Fraction(1, 3), Fraction(4, 9)},
            {Fraction(0, 1), Fraction(norm(f3_entry(0, 2)), 3),
             Fraction(M[0][2]**2, 9)}
        )

    def test_astrophysical_flat_fourier_washes_out_source_mixture(self):
        f3_born = tuple(
            tuple(norm(f3_entry(a, i)) for i in range(3))
            for a in range(3)
        )
        deco_num = tuple(
            tuple(sum(f3_born[a][i]*f3_born[b][i]
                      for i in range(3)) for b in range(3))
            for a in range(3)
        )
        self.assertEqual(deco_num, ((3, 3, 3),)*3)
        for source in ((1, 2, 0), (1, 0, 0)):
            total = sum(source)
            fractions = tuple(
                Fraction(sum(source[a]*deco_num[a][b] for a in range(3)),
                         9*total)
                for b in range(3)
            )
            self.assertEqual(fractions, (Fraction(1, 3),)*3)

    def test_astrophysical_rational_mixer_retains_some_source_information(self):
        born_nums = [[x*x for x in row] for row in M]
        deco_num = tuple(
            tuple(sum(born_nums[a][i]*born_nums[b][i]
                      for i in range(3)) for b in range(3))
            for a in range(3)
        )
        self.assertEqual(deco_num,
                         ((33, 24, 24), (24, 33, 24), (24, 24, 33)))
        pion, neutron = (1, 2, 0), (1, 0, 0)
        def at_earth(source):
            return tuple(Fraction(
                sum(source[a]*deco_num[a][b] for a in range(3)),
                81 * sum(source))
                for b in range(3))
        self.assertEqual(at_earth(pion),
                         (Fraction(9, 27), Fraction(10, 27), Fraction(8, 27)))
        self.assertEqual(at_earth(neutron),
                         (Fraction(11, 27), Fraction(8, 27), Fraction(8, 27)))

    def test_born_probability_cannot_be_signed_zero(self):
        # Additive cancellation yields exactly nonnegative Born intensity 0;
        # unlike signed ledgers, measured |amplitude|² has no +/- zero.
        self.assertEqual(norm(add(add(ONE, ZETA), ZETA2)), 0)
        self.assertNotEqual(norm(ONE), 0)


if __name__ == "__main__":
    unittest.main()
