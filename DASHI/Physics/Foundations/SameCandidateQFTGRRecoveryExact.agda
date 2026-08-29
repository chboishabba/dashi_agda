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

    microscopicState : Candidate → Effective.JointMicroscopicState
    coarseGrain : Candidate → Regime → Candidate

    -- Literal GR target already owned by the repository, together with an
    -- actual recovery operation from the SAME microscopic state.
    grTarget : Candidate → GR.EinsteinContinuumClosure
    recoverGR : Effective.JointMicroscopicState → GR.EinsteinContinuumClosure

    -- Literal constructive-QFT target already owned by the repository, again
    -- recovered from the SAME microscopic state.
    qftCarriers : QFT.LiteralYangMillsCarriers
    qftSemantics : QFT.LiteralYangMillsSemantics qftCarriers
    qftTarget : Candidate →
      QFT.LiteralYangMillsConstruction qftCarriers qftSemantics
    recoverQFT : Effective.JointMicroscopicState →
      QFT.LiteralYangMillsConstruction qftCarriers qftSemantics

    -- UV/IR labels do not prove a limit.  Applications declare the regimes.
    grRegime : Regime → Set
    qftRegime : Regime → Set

    -- Thin explicit convention transports into one common stress/source
    -- carrier.  The weld below compares the actual existing target objects.
    grStressToShared :
      ∀ candidate →
      FCG.ContinuumGeometry.Tensor2
        (FCG.ContinuumLorentzClosure.geometry
          (GR.EinsteinContinuumClosure.lorentzContinuum
            (grTarget candidate))) →
      SharedStressEnergy

    qftStressToShared : QFT.StressTensor qftCarriers → SharedStressEnergy

    BackreactionConsistent : Candidate → Regime → Set
    CorrectionsControlled : Candidate → Regime → Set

    unifiedPredicts : Candidate → Observable → Set
    establishedGRQFTPredicts : Observable → Set
    measurementTests : Measurement → Observable → Set

open UnifiedCandidate public

------------------------------------------------------------------------
-- Helpers exposing the literal source objects consumed by the weld.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Literal recovery receipts.
------------------------------------------------------------------------

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

    -- The recovery operation must commute with the candidate interpretation.
    recoveryCommutes : ∀ candidate →
      recoverGR U (microscopicState U candidate) ≡ grTarget U candidate

    recoveryAfterCoarseGrainingCommutes :
      ∀ candidate regime → grRegime U regime →
      recoverGR U (microscopicState U (coarseGrain U candidate regime))
        ≡ grTarget U (coarseGrain U candidate regime)

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

    recoveryCommutes : ∀ candidate →
      recoverQFT U (microscopicState U candidate) ≡ qftTarget U candidate

    recoveryAfterCoarseGrainingCommutes :
      ∀ candidate regime → qftRegime U regime →
      recoverQFT U (microscopicState U (coarseGrain U candidate regime))
        ≡ qftTarget U (coarseGrain U candidate regime)

open QFTRecoveryReceipt public

------------------------------------------------------------------------
-- Cross-sector receipts that neither separate recovery lane can supply alone.
------------------------------------------------------------------------

record SameStressEnergyWeld (U : UnifiedCandidate) : Set₁ where
  field
    -- The actual StressEnergy field from Bianchi/Lovelock and the actual
    -- stressTensor field from the literal QFT construction must agree after
    -- explicit convention transport, on the same candidate and overlap regime.
    sameStressEnergyOnOverlap :
      ∀ candidate regime group →
      grRegime U regime →
      qftRegime U regime →
      grStressToShared U (coarseGrain U candidate regime)
        (actualGRStressEnergy U (coarseGrain U candidate regime))
      ≡
      qftStressToShared U
        (actualQFTStressTensor U (coarseGrain U candidate regime) group)

open SameStressEnergyWeld public

record CommonRegimeRecovery (U : UnifiedCandidate) : Set₁ where
  field
    overlapRegime : Regime U
    overlapIsGR : grRegime U overlapRegime
    overlapIsQFT : qftRegime U overlapRegime

    -- Both sectors are evaluated after exactly the same coarse-graining map.
    backreactionConsistency : ∀ candidate →
      BackreactionConsistent U
        (coarseGrain U candidate overlapRegime) overlapRegime

    correctionControl : ∀ candidate →
      CorrectionsControlled U
        (coarseGrain U candidate overlapRegime) overlapRegime

open CommonRegimeRecovery public

record NovelObservableReceipt (U : UnifiedCandidate) : Set₁ where
  field
    candidate : Candidate U
    observable : Observable U
    predictedByUnifiedCandidate : unifiedPredicts U candidate observable
    excludedByEstablishedGRQFT : ¬ (establishedGRQFTPredicts U observable)

open NovelObservableReceipt public

record FalsifiableMeasurementReceipt
    (U : UnifiedCandidate)
    (novel : NovelObservableReceipt U) : Set₁ where
  field
    measurement : Measurement U
    testsNovelObservable :
      measurementTests U measurement (NovelObservableReceipt.observable novel)

open FalsifiableMeasurementReceipt public

------------------------------------------------------------------------
-- The complete same-candidate BIDI receipt.
------------------------------------------------------------------------

record SameCandidateQFTGRRecovery (U : UnifiedCandidate) : Set₁ where
  field
    grRecovery : GRRecoveryReceipt U
    qftRecovery : QFTRecoveryReceipt U
    stressEnergyWeld : SameStressEnergyWeld U
    regimeRecovery : CommonRegimeRecovery U
    novelObservable : NovelObservableReceipt U
    falsifiableMeasurement : FalsifiableMeasurementReceipt U novelObservable

open SameCandidateQFTGRRecovery public

------------------------------------------------------------------------
-- Exact handoff to the Stage-6/7 physical promotion consumer.
------------------------------------------------------------------------

physicalCandidateFromUnified :
  (U : UnifiedCandidate) → Physical.FundamentalPhysicalCandidate
physicalCandidateFromUnified U =
  Physical.fundamentalPhysicalCandidate
    (Candidate U)
    (GRRecoveryReceipt U × SameStressEnergyWeld U × CommonRegimeRecovery U)
    (QFTRecoveryReceipt U × SameStressEnergyWeld U × CommonRegimeRecovery U)
    (NovelObservableReceipt U)
    (Σ (NovelObservableReceipt U) λ novel →
       FalsifiableMeasurementReceipt U novel)

sameCandidateRecoveryImpliesPhysicalPromotion :
  ∀ {U : UnifiedCandidate} →
  SameCandidateQFTGRRecovery U →
  Physical.PhysicalPromotionGate (physicalCandidateFromUnified U)
sameCandidateRecoveryImpliesPhysicalPromotion recovery =
  ( grRecovery recovery
  , stressEnergyWeld recovery
  , regimeRecovery recovery )
  ,
  ( qftRecovery recovery
  , stressEnergyWeld recovery
  , regimeRecovery recovery )
  ,
  novelObservable recovery
  ,
  (novelObservable recovery , falsifiableMeasurement recovery)

------------------------------------------------------------------------
-- Fail-closed current-state theorem.
------------------------------------------------------------------------

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
