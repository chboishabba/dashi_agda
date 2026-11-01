{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CommonActionQFTGRContinuumProducerCompilerExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.CommonEffectiveActionVariationExact as Variation
import DASHI.Physics.Foundations.EinsteinCommonActionVariationFrontierExact as Einstein
import DASHI.Physics.Foundations.BalabanAllSectorContinuumProducerExact as Balaban

record CommonMetricProducerLanguage
    {U : Weld.UnifiedCandidate}
    {variation : Variation.CommonEffectiveActionVariation U}
    (grReceipt : Einstein.EinsteinTensorVariationReceipt variation)
    (qftProducer : Balaban.BalabanAllSectorContinuumProducer variation) : Set₁ where
  field
    MetricPerturbation VariationScalar : Set

    commonStressMetricPairing :
      Weld.SharedStressEnergy U → MetricPerturbation → VariationScalar

    toGRPerturbation :
      MetricPerturbation → Einstein.MetricPerturbation grReceipt

    toQFTPerturbation :
      MetricPerturbation → Balaban.MetricPerturbation qftProducer

    fromGRScalar : Einstein.VariationScalar grReceipt → VariationScalar
    fromQFTScalar : Balaban.VariationScalar qftProducer → VariationScalar

    grPairingCommutes :
      ∀ stress perturbation →
      commonStressMetricPairing stress perturbation
      ≡ fromGRScalar
          (Einstein.stressMetricPairing grReceipt
            stress (toGRPerturbation perturbation))

    qftPairingCommutes :
      ∀ stress perturbation →
      commonStressMetricPairing stress perturbation
      ≡ fromQFTScalar
          (Balaban.stressMetricPairing qftProducer
            stress (toQFTPerturbation perturbation))

    CommonAdmissibleMetricPerturbation :
      Weld.Candidate U → Weld.Regime U → MetricPerturbation → Set

    commonAdmissibleImpliesGRAdmissible :
      ∀ candidate regime perturbation →
      CommonAdmissibleMetricPerturbation candidate regime perturbation →
      Einstein.AdmissibleMetricPerturbation grReceipt
        candidate regime (toGRPerturbation perturbation)

    commonAdmissibleImpliesQFTAdmissible :
      ∀ candidate regime perturbation →
      CommonAdmissibleMetricPerturbation candidate regime perturbation →
      Balaban.CommonAdmissibleMetricPerturbation qftProducer
        candidate regime (toQFTPerturbation perturbation)

open CommonMetricProducerLanguage public

commonEinsteinAndBalabanProducerImpliesStressWeld :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U)
    (grReceipt : Einstein.EinsteinTensorVariationReceipt variation)
    (qftProducer : Balaban.BalabanAllSectorContinuumProducer variation) →
  CommonMetricProducerLanguage grReceipt qftProducer →
  Weld.StressEnergyWeldToken U →
  Weld.SameStressEnergyWeld U
commonEinsteinAndBalabanProducerImpliesStressWeld
    variation grReceipt qftProducer commonLanguage token =
  Variation.commonVariationImpliesStressWeld
    variation
    (Einstein.einsteinTensorVariationBuildsGRIdentification
      variation grReceipt)
    (Balaban.continuumProducerBuildsQFTVariationIdentification qftProducer)
    token

stressWeldImpliesCommonProducerPairingEquality :
  ∀ {U : Weld.UnifiedCandidate}
    {variation : Variation.CommonEffectiveActionVariation U}
    (grReceipt : Einstein.EinsteinTensorVariationReceipt variation)
    (qftProducer : Balaban.BalabanAllSectorContinuumProducer variation)
    (commonLanguage : CommonMetricProducerLanguage grReceipt qftProducer)
    (weld : Weld.SameStressEnergyWeld U) →
  ∀ candidate regime perturbation →
  Weld.grRegime U regime →
  Weld.qftRegime U regime →
  commonStressMetricPairing commonLanguage
    (Weld.grStressToShared U (Weld.coarseGrain U candidate regime)
      (Weld.actualGRStressEnergy U (Weld.coarseGrain U candidate regime)))
    perturbation
  ≡ commonStressMetricPairing commonLanguage
      (Weld.qftTotalStressShared U (Weld.coarseGrain U candidate regime))
      perturbation
stressWeldImpliesCommonProducerPairingEquality
    grReceipt qftProducer commonLanguage weld candidate regime perturbation
    grAtRegime qftAtRegime =
  cong
    (λ stress → commonStressMetricPairing commonLanguage stress perturbation)
    (Weld.sameStressEnergyOnOverlap weld
      candidate regime grAtRegime qftAtRegime)

commonActionQFTGRContinuumProducerCompilerLevel : ProofLevel
commonActionQFTGRContinuumProducerCompilerLevel = machineChecked

record ContinuumProducerCompilerBoundary : Set where
  constructor continuumProducerCompilerBoundary
  field
    commonMetricConsumerNeedsBalabanConvergenceInternals : Bool
    commonMetricConsumerNeedsBalabanConvergenceInternalsIsFalse :
      commonMetricConsumerNeedsBalabanConvergenceInternals ≡ false

    endpointProducerPlusCommonMetricLanguageIsSufficient : Bool
    endpointProducerPlusCommonMetricLanguageIsSufficientIsTrue :
      endpointProducerPlusCommonMetricLanguageIsSufficient ≡ true

canonicalContinuumProducerCompilerBoundary : ContinuumProducerCompilerBoundary
canonicalContinuumProducerCompilerBoundary =
  continuumProducerCompilerBoundary false refl true refl
