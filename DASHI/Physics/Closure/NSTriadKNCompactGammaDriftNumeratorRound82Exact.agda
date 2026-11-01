module DASHI.Physics.Closure.NSTriadKNCompactGammaDriftNumeratorRound82Exact where

------------------------------------------------------------------------
-- ROUND82 / COMPACT-GAMMA DRIFT NUMERATOR
--
-- For the resolved positive-transfer compact potential
--
--   B = Q / (Q + V),    V = 2 nu D,
--
-- the repository already has the division-free quotient derivative surface.
-- This file specializes that surface to exact rational algebra and proves the
-- sharper identity
--
--   Bdot (Q + V)^2 + Q Vdot = Qdot V,
--
-- equivalently
--
--   Bdot (Q + V)^2 = Qdot V - Q Vdot.
--
-- Therefore the C5 drift numerator is not a new spectral object: it is the
-- relative-growth competition between the nonlinear transfer Q and its viscous
-- denominator V.  The remaining PDE theorem must control that same-object
-- numerator (or its time integral) on dangerous selected events.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSNormalizedAlignmentBudgetDerivative as Quotient
import DASHI.Physics.Closure.NSCompactGammaPotentialDerivative as Compact

rationalBudgetProductArithmetic : Quotient.BudgetProductArithmetic
rationalBudgetProductArithmetic = record
  { Quotient.Scalar = ℚ
  ; Quotient._+_ = _+_
  ; Quotient._*_ = _*_
  ; Quotient.multiplyRightDistributesOverAddition = λ a b c →
      solve (a ∷ b ∷ c ∷ [])
  ; Quotient.swapMiddleFactors = λ a b c →
      solve (a ∷ b ∷ c ∷ [])
  }

expandedCompactGammaCrossRule :
  (I : Compact.CompactGammaDerivativeInputs rationalBudgetProductArithmetic) →
  Compact.Qdot I * (Compact.Q I + Compact.V I)
  ≡
  (Compact.Bdot I * (Compact.Q I + Compact.V I))
    * (Compact.Q I + Compact.V I)
  + Compact.Q I * (Compact.Qdot I + Compact.Vdot I)
expandedCompactGammaCrossRule I
  rewrite Compact.totalIsTransferPlusViscous I
        | Compact.totalDerivativeIsTransferPlusViscous I
  = Compact.compactGammaCrossMultipliedQuotientRule
      rationalBudgetProductArithmetic I

compactGammaDriftGrowthBalance :
  (I : Compact.CompactGammaDerivativeInputs rationalBudgetProductArithmetic) →
  (Compact.Bdot I * (Compact.Q I + Compact.V I))
    * (Compact.Q I + Compact.V I)
    + Compact.Q I * Compact.Vdot I
  ≡ Compact.Qdot I * Compact.V I
compactGammaDriftGrowthBalance I =
  let
    q = Compact.Q I
    v = Compact.V I
    qdot = Compact.Qdot I
    vdot = Compact.Vdot I
    bdot = Compact.Bdot I

    crossed = expandedCompactGammaCrossRule I

    cancelled = cong
      (λ value → value - q * qdot)
      crossed

    leftNormalize :
      qdot * (q + v) - q * qdot ≡ qdot * v
    leftNormalize = solve (q ∷ v ∷ qdot ∷ [])

    rightNormalize :
      ((bdot * (q + v)) * (q + v) + q * (qdot + vdot))
        - q * qdot
      ≡ (bdot * (q + v)) * (q + v) + q * vdot
    rightNormalize = solve (q ∷ v ∷ qdot ∷ vdot ∷ bdot ∷ [])
  in
  trans
    (sym rightNormalize)
    (trans (sym cancelled) leftNormalize)

compactGammaDriftNumeratorExact :
  (I : Compact.CompactGammaDerivativeInputs rationalBudgetProductArithmetic) →
  (Compact.Bdot I * (Compact.Q I + Compact.V I))
    * (Compact.Q I + Compact.V I)
  ≡ Compact.Qdot I * Compact.V I
    - Compact.Q I * Compact.Vdot I
compactGammaDriftNumeratorExact I =
  let
    q = Compact.Q I
    v = Compact.V I
    qdot = Compact.Qdot I
    vdot = Compact.Vdot I
    bdot = Compact.Bdot I

    balanced = compactGammaDriftGrowthBalance I
    shifted = cong
      (λ value → value - q * vdot)
      balanced

    leftNormalize :
      ((bdot * (q + v)) * (q + v) + q * vdot) - q * vdot
      ≡ (bdot * (q + v)) * (q + v)
    leftNormalize = solve (q ∷ v ∷ vdot ∷ bdot ∷ [])
  in
  trans
    (sym leftNormalize)
    shifted

round82CompactGammaDriftNumeratorIsRelativeGrowthCompetition : Bool
round82CompactGammaDriftNumeratorIsRelativeGrowthCompetition = true

round82PhysicalDangerousRelativeGrowthCoercivityConstructed : Bool
round82PhysicalDangerousRelativeGrowthCoercivityConstructed = false

round82CompactGammaDriftNumeratorIsRelativeGrowthCompetitionIsTrue :
  round82CompactGammaDriftNumeratorIsRelativeGrowthCompetition ≡ true
round82CompactGammaDriftNumeratorIsRelativeGrowthCompetitionIsTrue = refl
