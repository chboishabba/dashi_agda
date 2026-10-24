"""Independent three-flavour PMNS/finite-C4 mathematics regression.

Original numeric implementation authored for DASHI, 2026-10-24.
PDG matrix convention; published *inputs* from NuFIT 6.1 IC24+SK, NO.
Tests standard vacuum quantum mechanics only: NOT a NuFIT likelihood fit,
IceCube event reconstruction, mass-generation theorem, or physical
verification of any FactorVec/369 model.
"""
import cmath
from enum import Enum
from itertools import product
import math
import unittest

NUFIT_ROOT = "https://www.nu-fit.org/sites/default/files/v61.tbl-parameters.pdf"
ICECUBE_V2_ROOT = "https://github.com/icecube/skyllh/releases/tag/v26.1.0"
PHASE_CONSTANT = 1.2669328  # convention: sin²(1.2669328 Δm²[eV²] L[km]/E[GeV])
NORM_TOL = 5e-12

class DatasetKind(Enum):
    OSCILLATION_FIT = "NuFIT6.1_IC24_with_SK_normal_ordering"
    POINT_SOURCE_DR2_V1 = "IceTracks-DR2-v1"
    POINT_SOURCE_DR2_V2 = "IceTracks-DR2-v2"
    DEEPCORE_OSCILLATION = "IceCube-DeepCore-oscillation"


def require_oscillation_fit(dataset: DatasetKind) -> None:
    if dataset is not DatasetKind.OSCILLATION_FIT:
        raise ValueError("WrongType: source-search/DeepCore data are not NuFIT 6.1 mass-fit parameters")


def require_point_source_v2(dataset: DatasetKind) -> None:
    if dataset is not DatasetKind.POINT_SOURCE_DR2_V2:
        raise ValueError("WrongType or stale IRFs: require IceTracks-DR2-v2")


def pmns_pdg(theta12=33.76, theta13=8.62, theta23=43.29, delta_cp=212.0):
    """Standard PDG PMNS parameterisation (angles supplied in degrees).
    Majorana column phases not specified: they cancel from vacuum oscillations.
    """
    t12, t13, t23, d = map(math.radians, (theta12, theta13, theta23, delta_cp))
    s12, c12 = math.sin(t12), math.cos(t12)
    s13, c13 = math.sin(t13), math.cos(t13)
    s23, c23 = math.sin(t23), math.cos(t23)
    ep = cmath.exp(1j * d)
    em = ep.conjugate()
    return (
        (c12*c13, s12*c13, s13*em),
        (-s12*c23-c12*s23*s13*ep, c12*c23-s12*s23*s13*ep, s23*c13),
        (s12*s23-c12*c23*s13*ep, -c12*s23-s12*c23*s13*ep, c23*c13),
    )


def amplitude(u, masses_squared, alpha, beta, distance_km, energy_gev, antineutrino=False):
    if energy_gev <= 0 or distance_km < 0:
        raise ValueError("E must be positive; L nonnegative")
    return sum(
        (u[beta][i].conjugate() if antineutrino else u[beta][i])
        * (u[alpha][i] if antineutrino else u[alpha][i].conjugate())
        * cmath.exp(-2j * PHASE_CONSTANT * masses_squared[i] * distance_km / energy_gev)
        for i in range(3)
    )


def probability(u, masses_squared, alpha, beta, l_km, e_gev, antineutrino=False):
    return abs(amplitude(u, masses_squared, alpha, beta, l_km, e_gev, antineutrino)) ** 2


# Exact independent three-flavour rational orthogonal control used in Agda.
RATIONAL_U_NUM = ((1, 2, 2), (2, 1, -2), (2, -2, 1))
C4 = ((1, 0), (0, 1), (-1, 0), (0, -1))


def finite_amplitude_num(alpha, beta, phases):
    return (
        sum(RATIONAL_U_NUM[alpha][i]*RATIONAL_U_NUM[beta][i]*phases[i][0] for i in range(3)),
        sum(RATIONAL_U_NUM[alpha][i]*RATIONAL_U_NUM[beta][i]*phases[i][1] for i in range(3)),
    )


class NeutrinoThreeFlavourTests(unittest.TestCase):
    def setUp(self):
        self.u = pmns_pdg()
        self.masses = (0.0, 7.537e-5, 2.511e-3) # arbitrary common mass offset fixed to zero

    def test_pdg_pmns_is_unitary_to_roundoff(self):
        for a in range(3):
            for b in range(3):
                inner = sum(self.u[a][i]*self.u[b][i].conjugate() for i in range(3))
                self.assertAlmostEqual(abs(inner - (1 if a == b else 0)), 0, delta=NORM_TOL)

    def test_vacuum_probability_conservation_and_zero_distance(self):
        for length, energy in ((0, 1), (295, 0.6), (810, 2.0), (1300, 2.5)):
            for alpha in range(3):
                probs = [probability(self.u, self.masses, alpha, beta, length, energy)
                         for beta in range(3)]
                self.assertAlmostEqual(sum(probs), 1, delta=NORM_TOL)
                if length == 0:
                    for beta, p in enumerate(probs):
                        self.assertAlmostEqual(p, float(alpha == beta), delta=NORM_TOL)

    def test_common_mass_squared_shift_is_unobservable(self):
        shifted = tuple(x + 0.03 for x in self.masses)
        for alpha, beta in product(range(3), repeat=2):
            initial = probability(self.u, self.masses, alpha, beta, 1300, 2.5)
            shifted_p = probability(self.u, shifted, alpha, beta, 1300, 2.5)
            self.assertAlmostEqual(initial, shifted_p, delta=NORM_TOL)

    def test_field_rephasing_and_majorana_column_phase_invariance(self):
        rows = tuple(cmath.exp(1j*x) for x in (0.23, -0.77, 1.31))
        cols = tuple(cmath.exp(1j*x) for x in (-0.63, 0.39, 1.9))
        rephased = tuple(tuple(rows[a]*self.u[a][i]*cols[i] for i in range(3))
                         for a in range(3))
        for alpha, beta in product(range(3), repeat=2):
            self.assertAlmostEqual(
                probability(self.u, self.masses, alpha, beta, 1300, 2.5),
                probability(rephased, self.masses, alpha, beta, 1300, 2.5),
                delta=NORM_TOL
            )

    def test_vacuum_cp_conjugation(self):
        uc = pmns_pdg(delta_cp=-212.0)
        for alpha, beta in product(range(3), repeat=2):
            self.assertAlmostEqual(
                probability(self.u, self.masses, alpha, beta, 810, 2.0, antineutrino=True),
                probability(uc, self.masses, alpha, beta, 810, 2.0),
                delta=NORM_TOL
            )

    def test_dirac_cp_odd_discriminator_matches_phase_sum(self):
        # Vacuum CP-odd appearance difference is physically observable
        # in principle, unlike Majorana column rephasing.  No detector
        # sensitivity, confidence interval or measured CP violation claimed.
        alpha, beta, l_km, e_gev = 1, 0, 1300.0, 2.5
        c = [self.u[beta][i]*self.u[alpha][i].conjugate() for i in range(3)]
        predicted = 4*sum(
            (c[i]*c[j].conjugate()).imag
            * math.sin(2*PHASE_CONSTANT
                       *(self.masses[i]-self.masses[j])*l_km/e_gev)
            for i in range(3) for j in range(i)
        )
        difference = (
            probability(self.u, self.masses, alpha, beta, l_km, e_gev) -
            probability(self.u, self.masses, alpha, beta, l_km, e_gev,
                        antineutrino=True)
        )
        self.assertAlmostEqual(difference, predicted, delta=NORM_TOL)
        self.assertGreater(abs(difference), 1e-3)

    def test_exact_c4_three_flavour_norm_all_192_cases(self):
        for a in range(3):
            for phases in product(C4, repeat=3):
                normnums = []
                for b in range(3):
                    re, im = finite_amplitude_num(a, b, phases)
                    normnums.append(re*re + im*im)
                self.assertEqual(sum(normnums), 81)
        phases = (C4[0], C4[1], C4[3])
        self.assertEqual([sum(x*x for x in finite_amplitude_num(0,b,phases))
                          for b in range(3)], [1, 40, 40])

    def test_rational_mixer_gram_exact(self):
        for a, b in product(range(3), repeat=2):
            self.assertEqual(
                sum(RATIONAL_U_NUM[a][i]*RATIONAL_U_NUM[b][i] for i in range(3)),
                9 if a == b else 0
            )

    def test_declared_data_roles_cannot_be_interchanged(self):
        require_oscillation_fit(DatasetKind.OSCILLATION_FIT)
        require_point_source_v2(DatasetKind.POINT_SOURCE_DR2_V2)
        for bad in (DatasetKind.POINT_SOURCE_DR2_V1, DatasetKind.POINT_SOURCE_DR2_V2,
                    DatasetKind.DEEPCORE_OSCILLATION):
            with self.assertRaisesRegex(ValueError, "WrongType"):
                require_oscillation_fit(bad)
        with self.assertRaisesRegex(ValueError, "stale IRFs"):
            require_point_source_v2(DatasetKind.POINT_SOURCE_DR2_V1)
        with self.assertRaisesRegex(ValueError, "WrongType"):
            require_point_source_v2(DatasetKind.OSCILLATION_FIT)

    def test_normal_and_inverted_ordering_denominators_not_silently_swapped(self):
        # NuFIT 6.1: for IO the tabulated delta(m^2)3l is delta(m^2)32.
        io_m32 = -2.483e-3
        io_m31 = io_m32 + 7.537e-5
        self.assertLess(io_m31, 0)
        self.assertNotEqual(io_m31, io_m32)
        self.assertLess(7.537e-5 / io_m31, 0)
        self.assertGreater(7.537e-5 / abs(io_m31), 0)


if __name__ == "__main__":
    unittest.main()
