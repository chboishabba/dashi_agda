module DASHI.Analysis.BishopUnitIntervalMidpointExact where

------------------------------------------------------------------------
-- CANONICAL STRICT LARGER RATIO INSIDE THE BISHOP UNIT INTERVAL
--
-- For 0 <= r < 1 choose
--
--   s = (r + 1) / 2.
--
-- Then r < s < 1 constructively on the literal Bishop real carrier.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopArchimedeanLinearAbsorptionExact as Absorb
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit

midpointToOne : BishopReal.ℝ → BishopReal.ℝ
midpointToOne ratio =
  BishopReal._*_
    Exp.half
    (BishopReal._+_ ratio BishopReal.1ℝ)

ratioBelowMidpoint :
  ∀ {ratio} →
  Unit.BishopUnitIntervalRatio ratio →
  BishopReal._<_ ratio (midpointToOne ratio)
ratioBelowMidpoint {ratio} inputs =
  let
    doubled =
      BishopP.+-monoʳ-<
        ratio
        (Unit.ratioBelowOne inputs)

    scaled =
      BishopP.*-monoʳ-<-pos
        (BishopP.0<x⇒posx Exp.halfPositive)
        doubled

    leftMeaning :
      BishopReal._≃_
        (BishopReal._*_
          Exp.half
          (BishopReal._+_ ratio ratio))
        ratio
    leftMeaning =
      let open BishopP.ℝ-Solver
      in solve 1
        (λ r →
          Κ (+ 1 / 2) ⊗ (r ⊕ r)
          ⊜ r)
        BishopP.≃-refl ratio
  in
  BishopP.<-respˡ-≃
    leftMeaning
    scaled

midpointBelowOne :
  ∀ {ratio} →
  Unit.BishopUnitIntervalRatio ratio →
  BishopReal._<_ (midpointToOne ratio) BishopReal.1ℝ
midpointBelowOne {ratio} inputs =
  let
    summed =
      BishopP.+-monoʳ-<
        BishopReal.1ℝ
        (Unit.ratioBelowOne inputs)

    scaled =
      BishopP.*-monoʳ-<-pos
        (BishopP.0<x⇒posx Exp.halfPositive)
        summed

    leftCommute :
      BishopReal._≃_
        (BishopReal._*_
          Exp.half
          (BishopReal._+_ BishopReal.1ℝ ratio))
        (midpointToOne ratio)
    leftCommute =
      BishopP.*-congʳ
        (BishopP.+-comm BishopReal.1ℝ ratio)

    rightMeaning :
      BishopReal._≃_
        (BishopReal._*_
          Exp.half
          (BishopReal._+_ BishopReal.1ℝ BishopReal.1ℝ))
        BishopReal.1ℝ
    rightMeaning =
      let open BishopP.ℝ-Solver
      in solve 0
        (Κ (+ 1 / 2) ⊗ (Κ (+ 1 / 1) ⊕ Κ (+ 1 / 1))
          ⊜ Κ (+ 1 / 1))
        BishopP.≃-refl
  in
  BishopP.<-respʳ-≃ rightMeaning
    (BishopP.<-respˡ-≃ leftCommute scaled)

canonicalMidpointRatioPair :
  ∀ {ratio} →
  Unit.BishopUnitIntervalRatio ratio →
  Absorb.BishopStrictRatioPair
    ratio
    (midpointToOne ratio)
canonicalMidpointRatioPair inputs = record
  { ratioNonnegative = Unit.ratioNonnegative inputs
  ; ratioBelowLargerRatio = ratioBelowMidpoint inputs
  ; largerRatioBelowOne = midpointBelowOne inputs
  }
