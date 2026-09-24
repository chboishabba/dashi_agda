module DASHI.Moonshine.JInvariantEisensteinBishopMajorantSeriesExact where

------------------------------------------------------------------------
-- LITERAL EISENSTEIN-SHAPED BISHOP MAJORANT SERIES
--
-- DASHI CONTRIBUTION / CROSS-POLLINATION
--
-- The generic Analysis theorem already proves absolute convergence of
--
--   scale * (n+1)^k * r^(n+1)
--
-- for every fixed natural degree k, every nonnegative scale, and every Bishop
-- real r with 0 <= r < 1.
--
-- This owner performs only the Moonshine semantic specialization needed by the
-- literal E4/E6 increment envelopes:
--
--   E4: 240 (n+1)^4 r^(n+1)
--   E6: 504 (n+1)^6 r^(n+1).
--
-- No new convergence theorem, q-modulus theorem, or same-object transport is
-- introduced here.  The remaining application seam is precisely construction
-- of the Bishop ratio r from the literal q(tau) modulus and transport of the
-- already-owned increment inequalities onto this carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Analysis.BishopPolynomialGeometricSeriesConvergenceExact as PolyGeo
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NatReal
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit

e4Scale : BishopReal.ℝ
e4Scale = NatReal.natReal 240

e6Scale : BishopReal.ℝ
e6Scale = NatReal.natReal 504

e4ScaleNonnegative : BishopReal.NonNegative e4Scale
e4ScaleNonnegative = PolyGeo.natRealNonnegative 240

e6ScaleNonnegative : BishopReal.NonNegative e6Scale
e6ScaleNonnegative = PolyGeo.natRealNonnegative 504

e4MajorantTerm : BishopReal.ℝ → Nat → BishopReal.ℝ
e4MajorantTerm ratio =
  PolyGeo.shiftedScaledPolynomialGeometricTerm
    e4Scale ratio 4

e6MajorantTerm : BishopReal.ℝ → Nat → BishopReal.ℝ
e6MajorantTerm ratio =
  PolyGeo.shiftedScaledPolynomialGeometricTerm
    e6Scale ratio 6

e4MajorantAbsoluteConvergence :
  ∀ {ratio : BishopReal.ℝ} →
  Unit.BishopUnitIntervalRatio ratio →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (e4MajorantTerm ratio)
e4MajorantAbsoluteConvergence {ratio} inputs =
  PolyGeo.shiftedScaledPolynomialGeometricSeriesAbsolutelyConvergent
    ratio e4Scale 4
    (Unit.ratioNonnegative inputs)
    (Unit.ratioBelowOne inputs)
    e4ScaleNonnegative

e6MajorantAbsoluteConvergence :
  ∀ {ratio : BishopReal.ℝ} →
  Unit.BishopUnitIntervalRatio ratio →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (e6MajorantTerm ratio)
e6MajorantAbsoluteConvergence {ratio} inputs =
  PolyGeo.shiftedScaledPolynomialGeometricSeriesAbsolutelyConvergent
    ratio e6Scale 6
    (Unit.ratioNonnegative inputs)
    (Unit.ratioBelowOne inputs)
    e6ScaleNonnegative
