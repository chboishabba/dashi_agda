module DASHI.Law.SensibLawWoogarooQualityGainEvidenceCut20261106Exact where

-- EPBC 2019/8575, Cherish/Saunders Havill Preliminary Documentation
-- v5 (30 January 2026) Tables A62/A69/A76: exact conditional test.
-- Original 2012 Commonwealth Offsets assessment guide is the calculator
-- owner. Current National EPA official OAG instructions state:
-- "In most cases the difference in quality score ... is capped at 1 point.
-- Strong scientific evidence demonstrating a greater change is possible
-- is required to deviate from this figure."
--
-- The 1-point statement is GUIDANCE WITH EXPRESS EXCEPTION, not a
-- proved hard legal cap. This file does not rule that any reported
-- 2/3/4 point gain is impermissible: each one requires source-specific
-- scientific validation. Retain original QUT, QCC, RSPCA and consultant
-- authorship, and previous PR #1276 direct/indirect source ledgers.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawWoogarooKoalaOAGStatusSensitivity20261106Exact as Koala
import DASHI.Law.SensibLawWoogarooDecisiveOffsetTests20261106Exact as Tests

-- This is a finite conditional sensitivity operator, not an automatic
-- correction of official approved source. Each quality point has a
-- distinct species-/site-/time-/habitat justification obligation.
capOne : Nat → Nat
capOne zero = zero
capOne (suc _) = 1

capTwo : Nat → Nat
capTwo zero = zero
capTwo (suc zero) = 1
capTwo (suc (suc _)) = 2

capThree : Nat → Nat
capThree zero = zero
capThree (suc zero) = 1
capThree (suc (suc zero)) = 2
capThree (suc (suc (suc _))) = 3

cappedInput : (Nat → Nat) → List Koala.QualityRow → Nat
cappedInput cap [] = zero
cappedInput cap (r ∷ rs) =
  Koala.areaTenths r *
  cap (Koala.gainQualityPoints r) *
  Koala.futureConfidencePercent r +
  cappedInput cap rs

fullSourceCoefficient : Koala.inputSum Koala.allRows ≡ 1010350
fullSourceCoefficient = Koala.sourceWeightSum

onePointCoefficient : cappedInput capOne Koala.allRows ≡ 453625
onePointCoefficient = refl

twoPointCoefficient : cappedInput capTwo Koala.allRows ≡ 717325
twoPointCoefficient = refl

threePointCoefficient : cappedInput capThree Koala.allRows ≡ 882325
threePointCoefficient = refl

-- The original 2012 inverse-compounding OAG denominator is identical
-- across all 14 selected rows, holding p=0.002 and 20-year lag fixed.
-- Numeric percentages from the exact rational companion:
-- source: 108.345132619592...
-- cap 3: 94.616340019381...
-- cap 2: 76.922524131587...
-- cap 1: 48.644589285458...
-- The exact coefficients above certify the numerators. These figures
-- are NOT observed habitat quality, confidence bounds or legally
-- mandated restrictions on every offset AU.

data RequiredExceptionEvidence : Set where
  originalQualityTimeSeries : RequiredExceptionEvidence
  measuredBaselineAndCounterfactual : RequiredExceptionEvidence
  speciesAndAUSpecificMaturityModel : RequiredExceptionEvidence
  independentExpertValidation : RequiredExceptionEvidence
  actualDecisionSourceAndVersion : RequiredExceptionEvidence

record ExceptionalGainJustification : Set where
  constructor exceptional-gain-justification
  field
    originalEvidence : RequiredExceptionEvidence → Bool
    sourceReference : RequiredExceptionEvidence → Nat
    qualifiedIndependentReview : Bool

-- No justified-gain witness is constructed merely from source inputs.
-- No ecological/legal conclusion is derived from a conditional cap.

originalEcologicalChallenge : Tests.Challenge
originalEcologicalChallenge = Tests.challengeFor Tests.temporalSurvivalAndTimeLag
