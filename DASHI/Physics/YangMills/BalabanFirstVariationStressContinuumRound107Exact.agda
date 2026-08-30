{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFirstVariationStressContinuumRound107Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record ScalarLimitStructure (Cutoff Scalar : Set) : Set₁ where
  field
    ConvergesTo : (Cutoff → Scalar) → Scalar → Set
    convergenceCongruent :
      ∀ left right limit →
      (∀ cutoff → left cutoff ≡ right cutoff) →
      ConvergesTo left limit → ConvergesTo right limit
    limitUnique :
      ∀ sequence leftLimit rightLimit →
      ConvergesTo sequence leftLimit →
      ConvergesTo sequence rightLimit →
      leftLimit ≡ rightLimit
open ScalarLimitStructure public

record LiteralSectorStressContinuumReceipt
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C) : Set₁ where
  field
    MetricPerturbation VariationScalar : Set
    limits : ScalarLimitStructure (Top.Cutoff C) VariationScalar
    AdmissibleMetricPerturbation : MetricPerturbation → Set
    finiteFirstVariation : Top.Cutoff C → MetricPerturbation → VariationScalar
    finiteStressTensor : Top.Cutoff C → Top.StressTensor C
    stressMetricPairing :
      Top.StressTensor C → MetricPerturbation → VariationScalar
    continuumFirstVariation : MetricPerturbation → VariationScalar

    finiteVariationRepresentedByFiniteStress :
      ∀ cutoff perturbation →
      AdmissibleMetricPerturbation perturbation →
      finiteFirstVariation cutoff perturbation
      ≡ stressMetricPairing (finiteStressTensor cutoff) perturbation

    firstVariationConverges :
      ∀ perturbation →
      AdmissibleMetricPerturbation perturbation →
      ConvergesTo limits
        (λ cutoff → finiteFirstVariation cutoff perturbation)
        (continuumFirstVariation perturbation)

    finiteStressPairingConvergesToLiteralContinuumStress :
      ∀ perturbation →
      AdmissibleMetricPerturbation perturbation →
      ConvergesTo limits
        (λ cutoff → stressMetricPairing (finiteStressTensor cutoff) perturbation)
        (stressMetricPairing (Top.stressTensor Y group) perturbation)
open LiteralSectorStressContinuumReceipt public

continuumFirstVariationRepresentedByLiteralStress :
  ∀ {C S}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    (receipt : LiteralSectorStressContinuumReceipt Y group)
    perturbation →
  AdmissibleMetricPerturbation receipt perturbation →
  continuumFirstVariation receipt perturbation
  ≡ stressMetricPairing receipt (Top.stressTensor Y group) perturbation
continuumFirstVariationRepresentedByLiteralStress
    Y group receipt perturbation admissible =
  let
    finiteVariationSequence =
      λ cutoff → finiteFirstVariation receipt cutoff perturbation
    finiteStressSequence =
      λ cutoff → stressMetricPairing receipt
        (finiteStressTensor receipt cutoff) perturbation
    pointwise = λ cutoff →
      finiteVariationRepresentedByFiniteStress
        receipt cutoff perturbation admissible
    variationLimit = firstVariationConverges receipt perturbation admissible
    stressLimitOnVariationSequence =
      convergenceCongruent (limits receipt)
        finiteStressSequence finiteVariationSequence
        (stressMetricPairing receipt (Top.stressTensor Y group) perturbation)
        (λ cutoff → sym (pointwise cutoff))
        (finiteStressPairingConvergesToLiteralContinuumStress
          receipt perturbation admissible)
  in
  limitUnique (limits receipt)
    finiteVariationSequence
    (continuumFirstVariation receipt perturbation)
    (stressMetricPairing receipt (Top.stressTensor Y group) perturbation)
    variationLimit stressLimitOnVariationSequence

record StressContinuumBoundary : Set where
  constructor stressContinuumBoundary
  field
    finiteStressRepresentationAutomaticallySurvivesContinuumLimit : Bool
    finiteStressRepresentationAutomaticallySurvivesContinuumLimitIsFalse :
      finiteStressRepresentationAutomaticallySurvivesContinuumLimit ≡ false
    measureContinuumLimitAloneCommutesWithMetricDifferentiation : Bool
    measureContinuumLimitAloneCommutesWithMetricDifferentiationIsFalse :
      measureContinuumLimitAloneCommutesWithMetricDifferentiation ≡ false
    finiteRepresentationPlusTwoCompatibleLimitsClosesContinuumStress : Bool
    finiteRepresentationPlusTwoCompatibleLimitsClosesContinuumStressIsTrue :
      finiteRepresentationPlusTwoCompatibleLimitsClosesContinuumStress ≡ true

canonicalStressContinuumBoundary : StressContinuumBoundary
canonicalStressContinuumBoundary = stressContinuumBoundary false refl false refl true refl

stressContinuumCompilerLevel : ProofLevel
stressContinuumCompilerLevel = machineChecked

literalBalabanFirstVariationContinuumInterchangeLevel : ProofLevel
literalBalabanFirstVariationContinuumInterchangeLevel = conditional
