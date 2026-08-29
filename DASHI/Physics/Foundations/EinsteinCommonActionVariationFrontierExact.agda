module DASHI.Physics.Foundations.EinsteinCommonActionVariationFrontierExact where

open import DASHI.Core.Prelude

import DASHI.Physics.FiniteToContinuumGeometry as FCG
import DASHI.Physics.BianchiLovelockCompletion as GR
import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.CommonEffectiveActionVariationExact as Variation

actualGREinsteinTensor :
  ∀ (U : Weld.UnifiedCandidate) (candidate : Weld.Candidate U) →
  FCG.ContinuumGeometry.Tensor2
    (FCG.ContinuumLorentzClosure.geometry
      (GR.EinsteinContinuumClosure.lorentzContinuum
        (Weld.grTarget U candidate)))
actualGREinsteinTensor U candidate =
  GR.EinsteinTensorData.EinsteinTensor
    (GR.EinsteinContinuumClosure.tensors (Weld.grTarget U candidate))

actualGRFieldEquation :
  ∀ (U : Weld.UnifiedCandidate) (candidate : Weld.Candidate U) →
  actualGREinsteinTensor U candidate ≡ Weld.actualGRStressEnergy U candidate
actualGRFieldEquation U candidate =
  GR.BianchiLovelockClosure.fieldEquation
    (GR.EinsteinContinuumClosure.laws (Weld.grTarget U candidate))

record EinsteinTensorVariationReceipt
    {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U) : Set₁ where
  field
    MetricPerturbation VariationScalar : Set
    AdmissibleMetricPerturbation :
      Weld.Candidate U → Weld.Regime U → MetricPerturbation → Set
    stressMetricPairing :
      Weld.SharedStressEnergy U → MetricPerturbation → VariationScalar
    commonMetricFirstVariation :
      Weld.Candidate U → Weld.Regime U → MetricPerturbation → VariationScalar

    effectiveSourceRepresentsCommonMetricVariation :
      ∀ candidate regime perturbation →
      Weld.grRegime U regime →
      AdmissibleMetricPerturbation candidate regime perturbation →
      stressMetricPairing
        (Variation.effectiveSourceVariation variation
          (Weld.coarseGrain U candidate regime) regime)
        perturbation
      ≡ commonMetricFirstVariation candidate regime perturbation

    commonMetricVariationEqualsEinsteinPairing :
      ∀ candidate regime perturbation →
      Weld.grRegime U regime →
      AdmissibleMetricPerturbation candidate regime perturbation →
      commonMetricFirstVariation candidate regime perturbation
      ≡ stressMetricPairing
          (Weld.grStressToShared U (Weld.coarseGrain U candidate regime)
            (actualGREinsteinTensor U
              (Weld.coarseGrain U candidate regime)))
          perturbation

    pairingSeparatesStressOnAdmittedDomain :
      ∀ candidate regime left right →
      (∀ perturbation →
        AdmissibleMetricPerturbation candidate regime perturbation →
        stressMetricPairing left perturbation ≡ stressMetricPairing right perturbation) →
      left ≡ right
open EinsteinTensorVariationReceipt public

commonVariationEqualsEinsteinTensor :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U)
    (receipt : EinsteinTensorVariationReceipt variation)
    candidate regime →
  Weld.grRegime U regime →
  Variation.effectiveSourceVariation variation
    (Weld.coarseGrain U candidate regime) regime
  ≡ Weld.grStressToShared U (Weld.coarseGrain U candidate regime)
      (actualGREinsteinTensor U (Weld.coarseGrain U candidate regime))
commonVariationEqualsEinsteinTensor variation receipt candidate regime grAtRegime =
  pairingSeparatesStressOnAdmittedDomain
    receipt candidate regime
    (Variation.effectiveSourceVariation variation
      (Weld.coarseGrain U candidate regime) regime)
    (Weld.grStressToShared U (Weld.coarseGrain U candidate regime)
      (actualGREinsteinTensor U (Weld.coarseGrain U candidate regime)))
    (λ perturbation admissible →
      trans
        (effectiveSourceRepresentsCommonMetricVariation
          receipt candidate regime perturbation grAtRegime admissible)
        (commonMetricVariationEqualsEinsteinPairing
          receipt candidate regime perturbation grAtRegime admissible))

einsteinTensorVariationBuildsGRIdentification :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U) →
  EinsteinTensorVariationReceipt variation →
  Variation.EinsteinVariationIdentification variation
einsteinTensorVariationBuildsGRIdentification variation receipt = record
  { Variation.EinsteinVariationIdentification.variationEqualsEinsteinSource =
      λ candidate regime grAtRegime →
        let selected = Weld.coarseGrain U candidate regime
            fieldEquationShared =
              cong (Weld.grStressToShared U selected)
                (actualGRFieldEquation U selected)
            variationToEinstein =
              commonVariationEqualsEinsteinTensor
                variation receipt candidate regime grAtRegime
        in trans (sym fieldEquationShared) (sym variationToEinstein)
  }

record EinsteinVariationBoundary : Set where
  constructor einsteinVariationBoundary
  field
    fieldEquationAloneDerivesCommonAction : Bool
    fieldEquationAloneDerivesCommonActionIsFalse :
      fieldEquationAloneDerivesCommonAction ≡ false
    tensorNameAloneDeterminesMetricVariationFunctional : Bool
    tensorNameAloneDeterminesMetricVariationFunctionalIsFalse :
      tensorNameAloneDeterminesMetricVariationFunctional ≡ false
    equalityOfPairingsImpliesTensorEqualityWithoutSeparationTheorem : Bool
    equalityOfPairingsImpliesTensorEqualityWithoutSeparationTheoremIsFalse :
      equalityOfPairingsImpliesTensorEqualityWithoutSeparationTheorem ≡ false
    commonMetricVariationEqualsEinsteinPairingIsStillPhysicalTheorem : Bool
    commonMetricVariationEqualsEinsteinPairingIsStillPhysicalTheoremIsTrue :
      commonMetricVariationEqualsEinsteinPairingIsStillPhysicalTheorem ≡ true
    einsteinVariationPlusSeparationPlusFieldEquationBuildsGRSource : Bool
    einsteinVariationPlusSeparationPlusFieldEquationBuildsGRSourceIsTrue :
      einsteinVariationPlusSeparationPlusFieldEquationBuildsGRSource ≡ true

canonicalEinsteinVariationBoundary : EinsteinVariationBoundary
canonicalEinsteinVariationBoundary =
  einsteinVariationBoundary false refl false refl false refl true refl true refl
