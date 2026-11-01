module DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact where

open import DASHI.Core.Prelude

import DASHI.Physics.FiniteToContinuumGeometry as FCG
import DASHI.Physics.BianchiLovelockCompletion as GR
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT
import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as Geometry
import DASHI.Physics.Foundations.KernelQFTEmergenceObligations as Quantum
import DASHI.Physics.Foundations.UnifiedEffectiveActionBoundary as Effective
import DASHI.Physics.Foundations.PhysicalTheoryExperimentDiscriminationExact as Physical

------------------------------------------------------------------------
-- BIDI unification cut.
--
-- Backward consumer:
--   GR recovery + low-energy QFT recovery + novel observable + falsifiable
--   measurement.
--
-- Forward producers:
--   the existing joint microscopic/effective-action carrier, the continuum GR
--   closure, and the literal constructive-QFT carrier.
--
-- No physical recovery theorem is asserted here.  The module makes the exact
-- same-candidate receipts literal and proves that their conjunction feeds the
-- physical-promotion consumer without another semantic jump.
------------------------------------------------------------------------

record UnifiedCandidate : Set₂ where
  constructor unifiedCandidate
  field
    Candidate : Set
    Regime : Set
    Observable : Set
    Measurement : Set
    SharedStressEnergy : Set

    GRRecoveryToken : Set
    QFTRecoveryToken : Set
    StressEnergyWeldToken : Set
    RegimeRecoveryToken : Set
    NovelObservableToken : Set
    FalsifiableMeasurementToken : Set

    microscopicState : Candidate → Effective.JointMicroscopicState
    coarseGrain : Candidate → Regime → Candidate

    grTarget : Candidate → GR.EinsteinContinuumClosure
    recoverGR : Effective.JointMicroscopicState → GR.EinsteinContinuumClosure

    qftCarriers : QFT.LiteralYangMillsCarriers
    qftSemantics : QFT.LiteralYangMillsSemantics qftCarriers
    qftTarget : Candidate →
      QFT.LiteralYangMillsConstruction qftCarriers qftSemantics
    recoverQFT : Effective.JointMicroscopicState →
      QFT.LiteralYangMillsConstruction qftCarriers qftSemantics

    grRegime : Regime → Set
    qftRegime : Regime → Set

    grStressToShared :
      ∀ candidate →
      FCG.ContinuumGeometry.Tensor2
        (FCG.ContinuumLorentzClosure.geometry
          (GR.EinsteinContinuumClosure.lorentzContinuum
            (grTarget candidate))) →
      SharedStressEnergy

    -- The literal YM construction is indexed by compact simple gauge group.
    -- Those sector stresses must be aggregated before comparison with the
    -- total Einstein source.
    qftSectorStressToShared :
      QFT.CompactSimpleGroup qftCarriers →
      QFT.StressTensor qftCarriers →
      SharedStressEnergy

    qftTotalStressShared : Candidate → SharedStressEnergy

    QFTStressAggregation :
      Candidate →
      (QFT.CompactSimpleGroup qftCarriers → SharedStressEnergy) →
      SharedStressEnergy → Set

    BackreactionConsistent : Candidate → Regime → Set
    CorrectionsControlled : Candidate → Regime → Set

    unifiedPredicts : Candidate → Observable → Set
    establishedGRQFTPredicts : Observable → Set
    measurementTests : Measurement → Observable → Set

open UnifiedCandidate public

actualGRStressEnergy :
  ∀ (U : UnifiedCandidate) (candidate : Candidate U) →
  FCG.ContinuumGeometry.Tensor2
    (FCG.ContinuumLorentzClosure.geometry
      (GR.EinsteinContinuumClosure.lorentzContinuum
        (grTarget U candidate)))
actualGRStressEnergy U candidate =
  GR.EinsteinTensorData.StressEnergy
    (GR.EinsteinContinuumClosure.tensors (grTarget U candidate))

actualQFTStressTensor :
  ∀ (U : UnifiedCandidate) (candidate : Candidate U) →
  QFT.CompactSimpleGroup (qftCarriers U) →
  QFT.StressTensor (qftCarriers U)
actualQFTStressTensor U candidate group =
  QFT.stressTensor (qftTarget U candidate) group

actualQFTSectorStressShared :
  ∀ (U : UnifiedCandidate) (candidate : Candidate U) →
  QFT.CompactSimpleGroup (qftCarriers U) →
  SharedStressEnergy U
actualQFTSectorStressShared U candidate group =
  qftSectorStressToShared U group (actualQFTStressTensor U candidate group)

record GRRecoveryReceipt (U : UnifiedCandidate) : Set₁ where
  field
    geometryAdapter : Geometry.KernelGeometryAdapter

    continuumManifoldConstructed :
      Geometry.continuumManifoldConstructed geometryAdapter ≡ true
    lorentzianMetricConstructed :
      Geometry.lorentzianMetricConstructed geometryAdapter ≡ true
    tensorSourceConstructed :
      Geometry.tensorSourceConstructed geometryAdapter ≡ true
    bianchiIdentityProved :
      Geometry.bianchiIdentityProved geometryAdapter ≡ true
    covariantConservationProved :
      Geometry.covariantConservationProved geometryAdapter ≡ true
    equivalencePrincipleRecovered :
      Geometry.equivalencePrincipleRecovered geometryAdapter ≡ true
    geodesicLimitRecovered :
      Geometry.geodesicLimitRecovered geometryAdapter ≡ true
    gravitationalRadiationRecovered :
      Geometry.gravitationalRadiationRecovered geometryAdapter ≡ true
    einsteinEquationRecovered :
      Geometry.einsteinEquationRecovered geometryAdapter ≡ true
    correctionBoundProved :
      Geometry.correctionBoundProved geometryAdapter ≡ true

    grRecoveryCommutes : ∀ candidate →
      recoverGR U (microscopicState U candidate) ≡ grTarget U candidate

    grRecoveryAfterCoarseGrainingCommutes :
      ∀ candidate regime → grRegime U regime →
      recoverGR U (microscopicState U (coarseGrain U candidate regime))
        ≡ grTarget U (coarseGrain U candidate regime)

    grPromotionToken : GRRecoveryToken U

open GRRecoveryReceipt public

record QFTRecoveryReceipt (U : UnifiedCandidate) : Set₁ where
  field
    quantumAdapter : Quantum.KernelQFTAdapter

    hilbertStructureRecovered :
      Quantum.hilbertStructureRecovered quantumAdapter ≡ true
    relativisticLocalityRecovered :
      Quantum.relativisticLocalityRecovered quantumAdapter ≡ true
    spinorSectorRecovered :
      Quantum.spinorSectorRecovered quantumAdapter ≡ true
    localGaugeConnectionRecovered :
      Quantum.localGaugeConnectionRecovered quantumAdapter ≡ true
    fockConstructionRecovered :
      Quantum.fockConstructionRecovered quantumAdapter ≡ true
    stableParticlesRecovered :
      Quantum.stableParticlesRecovered quantumAdapter ≡ true
    standardModelRepresentationsRecovered :
      Quantum.standardModelRepresentationsRecovered quantumAdapter ≡ true
    anomaliesCancelled :
      Quantum.anomaliesCancelled quantumAdapter ≡ true
    continuumLimitProved :
      Quantum.continuumLimitProved quantumAdapter ≡ true

    qftRecoveryCommutes : ∀ candidate →
      recoverQFT U (microscopicState U candidate) ≡ qftTarget U candidate

    qftRecoveryAfterCoarseGrainingCommutes :
      ∀ candidate regime → qftRegime U regime →
      recoverQFT U (microscopicState U (coarseGrain U candidate regime))
        ≡ qftTarget U (coarseGrain U candidate regime)

    qftPromotionToken : QFTRecoveryToken U

open QFTRecoveryReceipt public

record SameStressEnergyWeld (U : UnifiedCandidate) : Set₁ where
  field
    qftStressAggregation : ∀ candidate →
      QFTStressAggregation U candidate
        (actualQFTSectorStressShared U candidate)
        (qftTotalStressShared U candidate)

    sameStressEnergyOnOverlap :
      ∀ candidate regime →
      grRegime U regime →
      qftRegime U regime →
      grStressToShared U (coarseGrain U candidate regime)
        (actualGRStressEnergy U (coarseGrain U candidate regime))
      ≡
      qftTotalStressShared U (coarseGrain U candidate regime)

    stressWeldPromotionToken : StressEnergyWeldToken U

open SameStressEnergyWeld public

record CommonRegimeRecovery (U : UnifiedCandidate) : Set₁ where
  field
    overlapRegime : Regime U
    overlapIsGR : grRegime U overlapRegime
    overlapIsQFT : qftRegime U overlapRegime

    backreactionConsistency : ∀ candidate →
      BackreactionConsistent U
        (coarseGrain U candidate overlapRegime) overlapRegime

    correctionControl : ∀ candidate →
      CorrectionsControlled U
        (coarseGrain U candidate overlapRegime) overlapRegime

    regimePromotionToken : RegimeRecoveryToken U

open CommonRegimeRecovery public

record NovelObservableReceipt (U : UnifiedCandidate) : Set₁ where
  field
    candidate : Candidate U
    observable : Observable U
    predictedByUnifiedCandidate : unifiedPredicts U candidate observable
    excludedByEstablishedGRQFT : ¬ (establishedGRQFTPredicts U observable)
    novelPromotionToken : NovelObservableToken U

open NovelObservableReceipt public

record FalsifiableMeasurementReceipt
    (U : UnifiedCandidate)
    (novel : NovelObservableReceipt U) : Set₁ where
  field
    measurement : Measurement U
    testsNovelObservable :
      measurementTests U measurement (NovelObservableReceipt.observable novel)
    measurementPromotionToken : FalsifiableMeasurementToken U

open FalsifiableMeasurementReceipt public

record SameCandidateQFTGRRecovery (U : UnifiedCandidate) : Set₁ where
  field
    grRecovery : GRRecoveryReceipt U
    qftRecovery : QFTRecoveryReceipt U
    stressEnergyWeld : SameStressEnergyWeld U
    regimeRecovery : CommonRegimeRecovery U
    novelObservable : NovelObservableReceipt U
    falsifiableMeasurement : FalsifiableMeasurementReceipt U novelObservable

open SameCandidateQFTGRRecovery public

physicalCandidateFromUnified :
  (U : UnifiedCandidate) → Physical.FundamentalPhysicalCandidate
physicalCandidateFromUnified U =
  Physical.fundamentalPhysicalCandidate
    (Candidate U)
    (GRRecoveryToken U × (StressEnergyWeldToken U × RegimeRecoveryToken U))
    (QFTRecoveryToken U × (StressEnergyWeldToken U × RegimeRecoveryToken U))
    (NovelObservableToken U)
    (FalsifiableMeasurementToken U)

sameCandidateRecoveryImpliesPhysicalPromotion :
  ∀ {U : UnifiedCandidate} →
  SameCandidateQFTGRRecovery U →
  Physical.PhysicalPromotionGate (physicalCandidateFromUnified U)
sameCandidateRecoveryImpliesPhysicalPromotion recovery =
  ( GRRecoveryReceipt.grPromotionToken (grRecovery recovery)
  , ( SameStressEnergyWeld.stressWeldPromotionToken (stressEnergyWeld recovery)
    , CommonRegimeRecovery.regimePromotionToken (regimeRecovery recovery) ) )
  ,
  ( ( QFTRecoveryReceipt.qftPromotionToken (qftRecovery recovery)
    , ( SameStressEnergyWeld.stressWeldPromotionToken (stressEnergyWeld recovery)
      , CommonRegimeRecovery.regimePromotionToken (regimeRecovery recovery) ) )
    , ( NovelObservableReceipt.novelPromotionToken (novelObservable recovery)
      , FalsifiableMeasurementReceipt.measurementPromotionToken
          (falsifiableMeasurement recovery) ) )

currentGeometryLimitStillOpen :
  Effective.geometryLimitProved Effective.currentEffectiveRecoveryReceipt ≡ false
currentGeometryLimitStillOpen = refl

currentQuantumLimitStillOpen :
  Effective.quantumLimitProved Effective.currentEffectiveRecoveryReceipt ≡ false
currentQuantumLimitStillOpen = refl

currentCommonCoarseGrainingStillOpen :
  Effective.commonCoarseGrainingProved Effective.currentEffectiveRecoveryReceipt ≡ false
currentCommonCoarseGrainingStillOpen = refl

currentBackreactionConsistencyStillOpen :
  Effective.backreactionConsistencyProved Effective.currentEffectiveRecoveryReceipt ≡ false
currentBackreactionConsistencyStillOpen = refl

currentCorrectionControlStillOpen :
  Effective.correctionsControlled Effective.currentEffectiveRecoveryReceipt ≡ false
currentCorrectionControlStillOpen = refl
