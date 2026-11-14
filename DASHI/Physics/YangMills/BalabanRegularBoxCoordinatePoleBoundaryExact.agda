module DASHI.Physics.YangMills.BalabanRegularBoxCoordinatePoleBoundaryExact where

-- Selected SOURCE box negative control. Excising the 16 all-inner
-- 4D boxes guarantees at least one OUTER coordinate, NOT that every
-- coordinate excludes zero. In particular the rank-one regular box
-- [1/2,1]×[0,1/2]×[0,1/2]×[0,1/2] contains the three coordinate
-- hyperplanes p1=p2=p3=0.
--
-- Hence one may not infer a strictly positive lower bound for EACH
-- individual sin²(p_mu/2), nor for the product of their reciprocals,
-- solely from Grid.allInner cell ≡ false. The correct denominator
-- for a lattice propagator is often the SUM hat(p)^2, which needs
-- its own original momentum-normalisation and analytic positivity.
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ)
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact as Orbit
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinIntegralCertificateExact as Integral

selectedRankOneRegularBox : Grid.GridCell4
selectedRankOneRegularBox =
  Grid.gridCell4 Grid.positiveOuter
    Grid.positiveInner Grid.positiveInner Grid.positiveInner

selectedRankOneIsRegular :
  Grid.allInner selectedRankOneRegularBox ≡ false
selectedRankOneIsRegular = refl

selectedRankOneOrbit :
  Orbit.orbitClass selectedRankOneRegularBox ≡ Orbit.oneOuter
selectedRankOneOrbit = refl

-- These are the LITERAL rational endpoints of the actual original
-- normalized grid boxes, not independently invented interval bounds.
originalOuterLowerIsHalf :
  Integral.lower (Grid.cellInterval Grid.positiveOuter) ≡ Grid.half
originalOuterLowerIsHalf = refl

originalInnerLowerIsZero :
  Integral.lower (Grid.cellInterval Grid.positiveInner) ≡ Grid.zero
originalInnerLowerIsZero = refl

originalInnerContainsZeroAtLeftBoundary :
  Integral.lower (Grid.cellInterval Grid.positiveInner) ≡ Grid.zero
originalInnerContainsZeroAtLeftBoundary = originalInnerLowerIsZero

selectedRankOneHasThreeInnerAxes :
  Grid.c1 selectedRankOneRegularBox ≡ Grid.positiveInner
selectedRankOneHasThreeInnerAxes = refl

-- On this BOX the rational normalized momenta p1,p2,p3 can equal
-- zero. Thus sin(p1/2), etc., can equal zero, and the unregularised
-- product inverse does not have a positive finite enclosure there.
--
-- No imported trig library or imaginary expression is postulated:
-- this module proves exactly the finite SOURCE geometry that blocks
-- the coordinatewise-denominator shortcut.
