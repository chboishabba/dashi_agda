module DASHI.Physics.Foundations.CommonActionQFTGRVariationCompilerExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.CommonEffectiveActionVariationExact as Variation
import DASHI.Physics.Foundations.EinsteinCommonActionVariationFrontierExact as EinsteinVariation
import DASHI.Physics.Foundations.BalabanCommonActionVariationFrontierExact as BalabanVariation

record CommonMetricVariationLanguage
    {U : Weld.UnifiedCandidate}
    {variation : Variation.CommonEffectiveActionVariation U}
    (grReceipt : EinsteinVariation.EinsteinTensorVariationReceipt variation)
    (qftReceipt : BalabanVariation.BalabanAllSectorVariationReceipt variation)
    : Set₁ where
  field
    MetricPerturbation VariationScalar : Set
    commonStressMetricPairing :
      Weld.SharedStressEnergy U → MetricPerturbation → VariationScalar
    toGRPerturbation :
      MetricPerturbation → EinsteinVariation.MetricPerturbation grReceipt
    toQFTPerturbation :
      MetricPerturbation → BalabanVariation.MetricPerturbation qftReceipt
    fromGRScalar : EinsteinVariation.VariationScalar grReceipt → VariationScalar
    fromQFTScalar : BalabanVariation.VariationScalar qftReceipt → VariationScalar

    grPairingCommutes :
      ∀ stress perturbation →
      commonStressMetricPairing stress perturbation
      ≡ fromGRScalar
          (EinsteinVariation.stressMetricPairing grReceipt
            stress (toGRPerturbation perturbation))

    qftPairingCommutes :
      ∀ stress perturbation →
      commonStressMetricPairing stress perturbation
      ≡ fromQFTScalar
          (BalabanVariation.stressMetricPairing qftReceipt
            stress (toQFTPerturbation perturbation))

    CommonAdmissibleMetricPerturbation :
      Weld.Candidate U → Weld.Regime U → MetricPerturbation → Set

    commonAdmissibleImpliesGRAdmissible :
      ∀ candidate regime perturbation →
      CommonAdmissibleMetricPerturbation candidate regime perturbation →
      EinsteinVariation.AdmissibleMetricPerturbation grReceipt
        candidate regime (toGRPerturbation perturbation)

    commonAdmissibleImpliesQFTAdmissible :
      ∀ candidate regime perturbation →
      CommonAdmissibleMetricPerturbation candidate regime perturbation →
      BalabanVariation.CommonAdmissibleMetricPerturbation qftReceipt
        candidate regime (toQFTPerturbation perturbation)
open CommonMetricVariationLanguage public

commonEinsteinAndBalabanVariationImpliesStressWeld :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : Variation.CommonEffectiveActionVariation U)
    (grReceipt : EinsteinVariation.EinsteinTensorVariationReceipt variation)
    (qftReceipt : BalabanVariation.BalabanAllSectorVariationReceipt variation) →
  CommonMetricVariationLanguage grReceipt qftReceipt →
  Weld.StressEnergyWeldToken U →
  Weld.SameStressEnergyWeld U
commonEinsteinAndBalabanVariationImpliesStressWeld
    variation grReceipt qftReceipt commonLanguage token =
  Variation.commonVariationImpliesStressWeld
    variation
    (EinsteinVariation.einsteinTensorVariationBuildsGRIdentification
      variation grReceipt)
    (BalabanVariation.balabanSectorFamilyBuildsQFTVariationIdentification
      variation qftReceipt)
    token

stressWeldImpliesCommonMetricPairingEquality :
  ∀ {U : Weld.UnifiedCandidate}
    {variation : Variation.CommonEffectiveActionVariation U}
    (grReceipt : EinsteinVariation.EinsteinTensorVariationReceipt variation)
    (qftReceipt : BalabanVariation.BalabanAllSectorVariationReceipt variation)
    (commonLanguage : CommonMetricVariationLanguage grReceipt qftReceipt)
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
stressWeldImpliesCommonMetricPairingEquality
    grReceipt qftReceipt commonLanguage weld candidate regime perturbation
    grAtRegime qftAtRegime =
  cong
    (λ stress → commonStressMetricPairing commonLanguage stress perturbation)
    (Weld.sameStressEnergyOnOverlap weld
      candidate regime grAtRegime qftAtRegime)

record CommonActionQFTGRCompilerBoundary : Set where
  constructor commonActionQFTGRCompilerBoundary
  field
    separateExtraStressWeldTheoremStillNeededAfterBothReceipts : Bool
    separateExtraStressWeldTheoremStillNeededAfterBothReceiptsIsFalse :
      separateExtraStressWeldTheoremStillNeededAfterBothReceipts ≡ false
    independentGRAndQFTMetricLanguagesAutomaticallyMeanSameVariation : Bool
    independentGRAndQFTMetricLanguagesAutomaticallyMeanSameVariationIsFalse :
      independentGRAndQFTMetricLanguagesAutomaticallyMeanSameVariation ≡ false
    onePureYangMillsSectorCanStandForTotalQFTStress : Bool
    onePureYangMillsSectorCanStandForTotalQFTStressIsFalse :
      onePureYangMillsSectorCanStandForTotalQFTStress ≡ false
    sharedMetricLanguagePlusBothReceiptsCompilesStressWeld : Bool
    sharedMetricLanguagePlusBothReceiptsCompilesStressWeldIsTrue :
      sharedMetricLanguagePlusBothReceiptsCompilesStressWeld ≡ true

canonicalCommonActionQFTGRCompilerBoundary : CommonActionQFTGRCompilerBoundary
canonicalCommonActionQFTGRCompilerBoundary =
  commonActionQFTGRCompilerBoundary false refl false refl false refl true refl
