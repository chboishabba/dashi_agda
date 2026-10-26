#!/usr/bin/env python3
"""Field Loom Biot–Savart re-use regression, not a new implementation of the law.

Production finite-wire source = existing scripts/psychotronics_field_loom_coils.py.
Formal Fourier inverse-curl owner =
  DASHI/Physics/Closure/NSTriadKNFourierBiotSavartExact.agda
  DASHI/Physics/Closure/NSTriadKNMaxwellFluidBiotSavartBridgeExact.agda
These are distinct representations; this script does NOT prove a Fourier/
free-space distributional limit or certify any physical instrument.

Independent off-axis reference: classical circular-loop magnetostatic
elliptic-integral solution (K, E), evaluated via SciPy, not another sampled
filament numerical integration. OpenStax Ling/Moebs/Sanny (2016) owns its
pedagogical Biot–Savart derivation, not the origin of the physical law.
NIST CODATA 2022: mu_0 is measured, not exact after SI 2019; the existing
model retains legacy mu_0=4*pi*1e-7 only to preserve illustration.
"""
from math import hypot, sqrt, pi, cos, sin
import unittest

from psychotronics_field_loom_coils import MU0, loop_b, pair_b


def analytic_on_axis(z, *, radius_m, centre_z_m, turns, ampere):
    dz = z - centre_z_m
    return MU0 * turns * ampere * radius_m**2 / (2*(radius_m**2 + dz**2)**1.5)


def analytic_off_axis(x, y, z, *, radius_m, centre_z_m, turns, ampere):
    """Reference B=(Bx,By,Bz) for ideal zero-thickness circular loop [T].

    SciPy ellipk(m), ellipe(m) take parameter m=k². Formula excludes source
    wire points; evaluate away from r=a,z=z0. On-axis handled separately.
    """
    try:
        from scipy.special import ellipk, ellipe
    except ImportError as exc:
        raise unittest.SkipTest('scipy.special needed for independent elliptic reference') from exc
    r = hypot(x, y)
    dz = z - centre_z_m
    a = radius_m
    if r < 1e-12:
        return (0.0, 0.0, analytic_on_axis(z, radius_m=a,
                centre_z_m=centre_z_m, turns=turns, ampere=ampere))
    q = (a + r)**2 + dz**2
    w = (a - r)**2 + dz**2
    if w < 1e-14:
        raise ValueError('singular ideal-filament observation point')
    m = 4*a*r/q
    k, e = ellipk(m), ellipe(m)
    factor = MU0 * turns * ampere / (2*pi*sqrt(q))
    bz = factor * (k + (a*a - r*r - dz*dz)*e/w)
    br = factor * dz/r * (-k + (a*a + r*r + dz*dz)*e/w)
    return (br*x/r, br*y/r, bz)


class ReuseAndReference(unittest.TestCase):
    """No new numerical Biot-Savart core: calls repo's existing one."""

    def test_exact_axis_for_separate_radii_currents(self):
        for radius in (.04, .1, .3):
            for current in (-1.2, .4, 2.5):
                for z in (-.05, 0., .08):
                    expected = analytic_on_axis(z, radius_m=radius,
                            centre_z_m=0, turns=101, ampere=current)
                    actual = loop_b(0,0,z,radius,0,101,current)
                    self.assertAlmostEqual(actual[2],expected,delta=abs(expected)*1e-11)
                    self.assertLess(abs(actual[0])+abs(actual[1]),1e-12)

    def test_offaxis_against_independent_elliptic_solution(self):
        sites = ((.025,-.015,.018),(.015,0,.04),(.045,.03,-.02),
                 (.001,.005,.017),(.07,-.02,.016))
        for xyz in sites:
            result = loop_b(*xyz,.1,0,137,1.25,steps=256)
            expected = analytic_off_axis(*xyz,radius_m=.1,
                        centre_z_m=0,turns=137,ampere=1.25)
            denom = max(1e-15, sqrt(sum(c*c for c in expected)))
            discrepancy = sqrt(sum((a-b)**2 for a,b in zip(result,expected)))/denom
            self.assertLess(discrepancy,1e-7)

    def test_pair_superposition_and_current_reversal(self):
        for xyz in ((0.,0.,0.),(.015,.01,.012)):
            lower = loop_b(*xyz,.1,-.05,100,1.)
            upper = loop_b(*xyz,.1,+.05,100,1.)
            combined = pair_b(*xyz)
            anti = pair_b(*xyz,anti=True)
            for i in range(3):
                self.assertAlmostEqual(combined[i],lower[i]+upper[i],delta=1e-13)
                self.assertAlmostEqual(anti[i],lower[i]-upper[i],delta=1e-13)
            rev = pair_b(*xyz,ampere=-1.)
            for a,b in zip(combined,rev):
                self.assertAlmostEqual(a,-b,delta=1e-13)

    def test_divergence_away_from_wire_is_small(self):
        for x,y,z in ((.012,.017,.015),(.035,-.008,.02),(.0,.0,.02)):
            h=.0001
            div=0.
            b=pair_b(x,y,z)
            for k in range(3):
                p=[x,y,z]; m=[x,y,z]
                p[k]+=h;m[k]-=h
                div+=(pair_b(*p)[k]-pair_b(*m)[k])/(2*h)
            # Relative to field strength over characteristic length 0.1m.
            self.assertLess(abs(div)*.1/max(1e-15,sqrt(sum(t*t for t in b))),2e-4)

    def test_reject_nonfinite_or_invalid_coil_inputs(self):
        for args in (
            (float('nan'),0.,0.,.1,0.,100,1.),
            (0.,0.,0.,float('nan'),0.,100,1.),
            (0.,0.,0.,.1,0.,-100,1.),
            (0.,0.,0.,.1,0.,100,float('inf')),
        ):
            with self.assertRaises(ValueError):
                loop_b(*args)
        with self.assertRaises(ValueError):
            loop_b(0.,0.,0.,.1,0.,100,1.,steps=8)

    def test_reject_ideal_wire_singularity(self):
        with self.assertRaises(ValueError):
            theta=pi/256  # first existing midpoint quadrature segment
            loop_b(.1*cos(theta),.1*sin(theta),0.,.1,0.,100,1.)

if __name__ == '__main__':
    unittest.main(verbosity=2)
