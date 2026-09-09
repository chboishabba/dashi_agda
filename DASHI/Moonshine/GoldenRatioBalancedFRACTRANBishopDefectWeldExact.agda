module DASHI.Moonshine.GoldenRatioBalancedFRACTRANBishopDefectWeldExact where

------------------------------------------------------------------------
-- EXACT ℚᵘ -> BISHOP DEFECT WELD
--
-- The rational owner already proves on every balanced-FRACTRAN macro state
--
--   r_Q^2 - r_Q - 1 ~= 1/q^2.
--
-- This module transports that theorem through the vendored Bishop embedding.
-- No new analytic estimate is introduced: multiplication/subtraction
-- compatibility is exactly the existing RealProperties morphism surface.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _-_; -_; _*_; _≃_)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Moonshine.GoldenRatioBalancedFRACTRANBishopRatioCarrierExact as Ratio
import DASHI.Moonshine.GoldenRatioBalancedFRACTRANRationalDefectExact as RationalDefect
import DASHI.Moonshine.GoldenRatioBalancedFRACTRANReciprocalSquareConvergenceExact as Reciprocal

------------------------------------------------------------------------
-- 1. Generic embedding compatibility for the quadratic defect.
------------------------------------------------------------------------

embed : ℚᵘ → BishopReal.ℝ
embed = BishopReal._⋆

rationalDefect : ℚᵘ → ℚᵘ
rationalDefect r = ((r ℚ.* r) ℚ.- r) ℚ.- RationalDefect.oneQ

bishopDefect : ℚᵘ → BishopReal.ℝ
bishopDefect r =
  BishopReal._-_
    (BishopReal._-_
      (BishopReal._*_ (embed r) (embed r))
      (embed r))
    (embed RationalDefect.oneQ)

embeddedSquareMinusSelf :
  (r : ℚᵘ) →
  BishopReal._≃_
    (embed ((r ℚ.* r) ℚ.- r))
    (BishopReal._-_
      (BishopReal._*_ (embed r) (embed r))
      (embed r))
embeddedSquareMinusSelf r =
  BishopP.≃-trans
    (BishopP.⋆-distrib-to-p⋆-q⋆ (r ℚ.* r) r)
    (BishopP.+-congˡ
      (BishopReal.- (embed r))
      (BishopP.⋆-distrib-* r r))

embeddedDefectCompatibility :
  (r : ℚᵘ) →
  BishopReal._≃_
    (embed (rationalDefect r))
    (bishopDefect r)
embeddedDefectCompatibility r =
  BishopP.≃-trans
    (BishopP.⋆-distrib-to-p⋆-q⋆
      ((r ℚ.* r) ℚ.- r)
      RationalDefect.oneQ)
    (BishopP.+-congˡ
      (BishopReal.- (embed RationalDefect.oneQ))
      (embeddedSquareMinusSelf r))

------------------------------------------------------------------------
-- 2. Same reciprocal-square coordinate as the convergence owner.
------------------------------------------------------------------------

macroPair : Nat → Ratio.PositiveFibPair
macroPair = Ratio.iteratePositiveMacro

macroDenominator : Nat → Nat
macroDenominator n = Ratio.positiveLo (macroPair n)

rationalReciprocalSquareAgrees :
  (n : Nat) →
  RationalDefect.reciprocalSquareQ (macroDenominator n)
  ≡ Reciprocal.reciprocalSquareRational n
rationalReciprocalSquareAgrees n = refl

------------------------------------------------------------------------
-- 3. Every macro quadratic defect is exactly the already-convergent Bishop
--    reciprocal-square sequence.
------------------------------------------------------------------------

macroBishopDefect : Nat → BishopReal.ℝ
macroBishopDefect n =
  bishopDefect (Ratio.positiveRatioRational (macroPair n))

macroBishopDefectEqualsReciprocalSquare :
  (n : Nat) →
  BishopReal._≃_
    (macroBishopDefect n)
    (Reciprocal.reciprocalSquareBishop n)
macroBishopDefectEqualsReciprocalSquare n =
  BishopP.≃-trans
    (BishopP.≃-symm
      (embeddedDefectCompatibility
        (Ratio.positiveRatioRational (macroPair n))))
    (BishopP.≃-trans
      (BishopP.⋆-cong (RationalDefect.macroRatioDefect n))
      (BishopP.⋆-cong
        (ℚP.≃-reflexive (rationalReciprocalSquareAgrees n))))

------------------------------------------------------------------------
-- 4. Frontier.
------------------------------------------------------------------------

record BishopDefectWeldFrontier : Set where
  constructor bishop-defect-weld-frontier
  field
    rationalDefectExact : Bool
    bishopEmbeddingPreservesDefectExpression : Bool
    sameReciprocalSquareAsConvergenceOwner : Bool
    macroBishopDefectEqualsConvergentSequence : Bool
    conjugateFactorLowerBoundPaid : Bool
    finalRatioLimitPaid : Bool

canonicalBishopDefectWeldFrontier : BishopDefectWeldFrontier
canonicalBishopDefectWeldFrontier =
  bishop-defect-weld-frontier true true true true false false
