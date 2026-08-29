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
-- The point of this file is NOT to assert that the current kernel already
-- supplies these receipts.  It makes the missing same-candidate mathematics
-- literal, and proves that once those receipts are inhabited they feed the
-- physical-promotion gate without an additional semantic jump.
------------------------------------------------------------------------

record UnifiedCandidate : Set₂ where
  constructor unifiedCandidate
  field
    Candidate : Set
    Regime : Set
    Observable : Set
    Measurement : Set
    SharedStressEnergy : Set

    -- The same microscopic candidate is interpreted by the already-existing
    -- joint geometry/matter producer.
    microscopicState : Candidate → Effective.JointMicroscopicState

    -- Literal GR target already owned by the repository.
    grTarget : Candidate → GR.EinsteinContinuumClosure

    -- Literal constructive-QFT target already owned by the repository.
    qftCarriers : QFT.LiteralYangMillsCarriers
    qftSemantics : QFT.LiteralYangMillsSemantics qftCarriers
    qftTarget : Candidate →
      QFT.LiteralYangMillsConstruction qftCarriers qftSemantics

    -- UV/IR names are not used as proofs.  Applications declare the actual
    -- regimes on which the recovery theorems hold.
    grRegime : Regime → Set
    qftRegime : Regime → Set

    -- Both recovered sectors must map their stress/source object into ONE
    -- shared carrier before equality can even be asked.
    grStressEnergy : Candidate → SharedStressEnergy
    qftStressEnergy : Candidate → SharedStressEnergy

    -- The source identifications prevent an arbitrary common carrier from
    -- being mistaken for the actual Einstein source or QFT stress tensor.
    grStressRepresentsRecoveredEinsteinSource : Candidate → Set
    qftStressRepresentsRecoveredQFTStressTensor : Candidate → Set

    unifiedPredicts : Candidate → Observable → Set
    establishedGRQFTPredicts : Observable → Set
    measurementTests : Measurement → Observable → Set

open UnifiedCandidate public

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

    -- The produced object is the repository's literal continuum Einstein
    -- closure, not merely a similarly named metric model.
    sameGRTarget : ∀ candidate → Set
    sameGRTargetProved : ∀ candidate → sameGRTarget candidate

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

    -- Again, the recovery theorem must land in the same literal QFT object
    -- carried by U, rather than in a merely analogous finite gauge system.
    sameQFTTarget : ∀ candidate → Set
    sameQFTTargetProved : ∀ candidate → sameQFTTarget candidate

open QFTRecoveryReceipt public

------------------------------------------------------------------------
-- Cross-sector receipts that neither separate recovery lane can supply alone.
------------------------------------------------------------------------

record SameStressEnergyWeld (U : UnifiedCandidate) : Set₁ where
  field
    grSourceIdentification :
      ∀ candidate → grStressRepresentsRecoveredEinsteinSource U candidate
    qftStressIdentification :
      ∀ candidate → qftStressRepresentsRecoveredQFTStressTensor U candidate

    -- Same candidate + same declared overlap regime + same shared stress/source
    -- carrier.  This is the literal missing seam.
    sameStressEnergyOnOverlap :
      ∀ candidate regime →
      grRegime U regime →
      qftRegime U regime →
      grStressEnergy U candidate ≡ qftStressEnergy U candidate

open SameStressEnergyWeld public

record CommonRegimeRecovery (U : UnifiedCandidate) : Set₁ where
  field
    grRegimeInhabited : Set
    qftRegimeInhabited : Set
    overlapRegimeInhabited : Set

    grRegimeWitness : grRegimeInhabited
    qftRegimeWitness : qftRegimeInhabited
    overlapRegimeWitness : overlapRegimeInhabited

    commonCoarseGrainingProved : Set
    backreactionConsistencyProved : Set
    correctionsControlled : Set

    commonCoarseGrainingReceipt : commonCoarseGrainingProved
    backreactionConsistencyReceipt : backreactionConsistencyProved
    correctionsControlledReceipt : correctionsControlled

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
--
-- The existing effective-action receipt still records every bridge bit as
-- false.  This theorem deliberately does not manufacture a recovery witness
-- from it.  The next mathematical work is to replace those false bits by
-- theorem-bearing receipts on this exact interface.
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
