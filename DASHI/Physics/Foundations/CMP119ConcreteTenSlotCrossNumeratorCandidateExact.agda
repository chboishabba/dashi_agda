{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119ConcreteTenSlotCrossNumeratorCandidateExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; +_; -[1+_]; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver as ℚRing\nopen import Data.Product using (_×_; _,_)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanNormalizedExpectationCrossNumeratorExact as Cross
import DASHI.Physics.YangMills.BalabanLiteralDensityNormalizedSourceRound121Exact as R121
import DASHI.Physics.YangMills.BalabanNormalizedStressInsertionRound116Exact as R116

------------------------------------------------------------------------
-- CONCRETE TEN-SLOT NORMALIZED-CROSS-NUMERATOR CANDIDATE
--
-- This is deliberately a constructive candidate on the literal beta-driven
-- Density carrier, not a promotion of the published CMP119 expectation
-- semantics.  We choose
--
--   N = 0, Z = 1, dZ = 0, dN(h_ab) = target_ab,
--
-- so the division-free normalized derivative is exactly target_ab.
--
-- The remaining physical/source theorem is therefore not "find ten numbers".
-- It is the same-object identification saying that this concrete normalized
-- source is the actual CMP119 numerator/denominator/metric-derivative source.
------------------------------------------------------------------------

slotTarget : K.SymmetricTensorComponent4 → ℚ
slotTarget K.component00 = + 1
slotTarget K.component01 = 0ℚ
slotTarget K.component02 = 0ℚ
slotTarget K.component03 = 0ℚ
slotTarget K.component11 = -[1+ zero ]
slotTarget K.component12 = 0ℚ
slotTarget K.component13 = 0ℚ
slotTarget K.component22 = -[1+ zero ]
slotTarget K.component23 = 0ℚ
slotTarget K.component33 = -[1+ zero ]

normalizedCrossTargetIdentity :
  ∀ target →
  Cross.normalizedCrossNumerator 0ℚ (+ 1) target 0ℚ ≡ target
normalizedCrossTargetIdentity = ℚRing.solve-∀

concreteTenSlotNormalizedSource :
  ∀ {trajectory split}
    (inputs : Beta.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}) →
  R121.LiteralDensityNormalizedStressSource inputs
concreteTenSlotNormalizedSource inputs = record
  { R121.LiteralDensityNormalizedStressSource.MetricPerturbation =
      K.SymmetricTensorComponent4
  ; R121.LiteralDensityNormalizedStressSource.numerator =
      λ _ → 0ℚ
  ; R121.LiteralDensityNormalizedStressSource.denominator =
      λ _ → + 1
  ; R121.LiteralDensityNormalizedStressSource.numeratorDerivative =
      λ _ component → slotTarget component
  ; R121.LiteralDensityNormalizedStressSource.denominatorDerivative =
      λ _ _ → 0ℚ
  ; R121.LiteralDensityNormalizedStressSource.connectedInsertionNumerator =
      λ _ component → slotTarget component
  ; R121.LiteralDensityNormalizedStressSource.normalizedCrossNumeratorIsConnectedInsertion =
      λ _ component → normalizedCrossTargetIdentity (slotTarget component)
  }

crossDataAt :
  ∀ {trajectory split}
    (inputs : Beta.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}) →
  (scale : Nat) →
  K.SymmetricTensorComponent4 →
  R116.NormalizedSourceDerivativeCrossData
crossDataAt inputs scale component =
  R121.crossDataAt (concreteTenSlotNormalizedSource inputs) scale component

crossNumeratorAt :
  ∀ {trajectory split}
    (inputs : Beta.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}) →
  Nat →
  K.SymmetricTensorComponent4 →
  ℚ
crossNumeratorAt inputs scale component =
  R116.sourceDerivativeCrossNumerator (crossDataAt inputs scale component)

crossNumeratorComputesTarget :
  ∀ {trajectory split}
    (inputs : Beta.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split})
    scale component →
  crossNumeratorAt inputs scale component ≡ slotTarget component
crossNumeratorComputesTarget inputs scale component =
  R121.literalDensityCrossNumeratorIsConnectedInsertion
    (concreteTenSlotNormalizedSource inputs) scale component

tenComputedTargets :
  ∀ {trajectory split}
    (inputs : Beta.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split})
    scale →
  crossNumeratorAt inputs scale K.component00 ≡ + 1
  × crossNumeratorAt inputs scale K.component01 ≡ 0ℚ
  × crossNumeratorAt inputs scale K.component02 ≡ 0ℚ
  × crossNumeratorAt inputs scale K.component03 ≡ 0ℚ
  × crossNumeratorAt inputs scale K.component11 ≡ -[1+ zero ]
  × crossNumeratorAt inputs scale K.component12 ≡ 0ℚ
  × crossNumeratorAt inputs scale K.component13 ≡ 0ℚ
  × crossNumeratorAt inputs scale K.component22 ≡ -[1+ zero ]
  × crossNumeratorAt inputs scale K.component23 ≡ 0ℚ
  × crossNumeratorAt inputs scale K.component33 ≡ -[1+ zero ]
tenComputedTargets inputs scale =
  crossNumeratorComputesTarget inputs scale K.component00 ,
  crossNumeratorComputesTarget inputs scale K.component01 ,
  crossNumeratorComputesTarget inputs scale K.component02 ,
  crossNumeratorComputesTarget inputs scale K.component03 ,
  crossNumeratorComputesTarget inputs scale K.component11 ,
  crossNumeratorComputesTarget inputs scale K.component12 ,
  crossNumeratorComputesTarget inputs scale K.component13 ,
  crossNumeratorComputesTarget inputs scale K.component22 ,
  crossNumeratorComputesTarget inputs scale K.component23 ,
  crossNumeratorComputesTarget inputs scale K.component33

activeStressTarget : ℚ
activeStressTarget =
  slotTarget K.component00
  + slotTarget K.component11
  + slotTarget K.component22
  + slotTarget K.component33

activeStressTargetIsNegativeTwo :
  activeStressTarget ≡ -[1+ suc zero ]
activeStressTargetIsNegativeTwo = refl
