module DASHI.Physics.ExoticGravity.AntigravityOptimizedAcquisitionPlanExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Physics.ExoticGravity.AntigravitySharedSourceProofSearchExact as Shared
import DASHI.Physics.ExoticGravity.SuperconductingGravityExperimentSearchHypergraphExact as Hyper
import DASHI.Physics.ExoticGravity.SuperconductingSourceConstitutiveEvidenceBidiExact as Evidence
import DASHI.Physics.ExoticGravity.SuperconductingGravityCouplingResidualBidiExact as Coupling
import DASHI.Physics.ExoticGravity.LiTorrStandardGRComparatorBidiExact as GRComparator
import DASHI.Physics.ExoticGravity.LiTorrGeometryAcquisitionBidiExact as Geometry
import DASHI.Physics.ExoticGravity.SuperconductingSourceVsConstitutiveEnhancementBidiExact as Enhancement

------------------------------------------------------------------------
-- OPTIMIZED SAME-APPARATUS ACQUISITION PLAN
--
-- The plan is a sequence of payment targets, not a sequence of asserted
-- experimental successes.  Each bundle can advance several existing state
-- machines only if a real receipt carries the exact per-consumer witnesses.
------------------------------------------------------------------------

record FullSourceGeometryBundleReceipt : Set where
  constructor full-source-geometry-bundle-receipt
  field
    apparatusCarrier : String

    evidenceState : Evidence.EvidenceClosureState
    evidenceSourceCharacterised : Evidence.sourceCharacterised evidenceState ≡ true

    couplingState : Coupling.AlphaClosureState
    couplingSourceObservable : Coupling.sourceObservableOwned couplingState ≡ true

    comparatorState : GRComparator.GRComparatorState
    comparatorGeometry : GRComparator.geometryOwned comparatorState ≡ true
    comparatorStressEnergy : GRComparator.stressEnergyOwned comparatorState ≡ true
    comparatorMassCurrent : GRComparator.massCurrentOwned comparatorState ≡ true
    comparatorProbeGeometry : GRComparator.probeGeometryOwned comparatorState ≡ true

    geometryState : Geometry.GeometryClosureState
    sourceShape : Geometry.sourceShapeOwned geometryState ≡ true
    sourceMass : Geometry.sourceMassOwned geometryState ≡ true
    sourceRadius : Geometry.sourceRadiusOwned geometryState ≡ true
    sourceAngularVelocity : Geometry.sourceAngularVelocityOwned geometryState ≡ true
    coherentMassCurrent : Geometry.coherentMassCurrentOwned geometryState ≡ true
    driveWaveform : Geometry.driveWaveformOwned geometryState ≡ true
    probeLocation : Geometry.probeLocationOwned geometryState ≡ true
    materialState : Geometry.materialStateOwned geometryState ≡ true

    enhancementState : Enhancement.EnhancementClosureState
    enhancementSourceCurrent : Enhancement.sourceCurrentOwned enhancementState ≡ true
    enhancementStressEnergy : Enhancement.sourceStressEnergyOwned enhancementState ≡ true
    enhancementGeometry : Enhancement.geometryOwned enhancementState ≡ true

open FullSourceGeometryBundleReceipt public

data FullSourceGeometryBundleAuthority : Set where

candidateSourceMoveDoesNotCreateFullBundle :
  FullSourceGeometryBundleAuthority → ⊥
candidateSourceMoveDoesNotCreateFullBundle ()

sourceBundleCandidateMove : Choice.InformationMove
sourceBundleCandidateMove = Hyper.characteriseSourceMove

postSourceEvidenceState : Evidence.EvidenceClosureState
postSourceEvidenceState =
  Evidence.evidence-closure-state true false true false true false

postSourceCouplingState : Coupling.AlphaClosureState
postSourceCouplingState =
  Coupling.alpha-closure-state true false false false false false false

postSourceComparatorState : GRComparator.GRComparatorState
postSourceComparatorState =
  GRComparator.gr-comparator-state true true true true false false

postSourceGeometryState : Geometry.GeometryClosureState
postSourceGeometryState =
  Geometry.geometry-closure-state true true true true true true true true

postSourceEnhancementState : Enhancement.EnhancementClosureState
postSourceEnhancementState =
  Enhancement.enhancement-closure-state true true true false false false

postSourceEvidenceFirstOpen :
  Evidence.firstOpenEvidenceLeaf postSourceEvidenceState
    ≡ Evidence.transitionLockLeaf
postSourceEvidenceFirstOpen = refl

postSourceCouplingFirstOpen :
  Coupling.firstOpenAlphaLeaf postSourceCouplingState
    ≡ Coupling.externalProbeLeaf
postSourceCouplingFirstOpen = refl

postSourceComparatorFirstOpen :
  GRComparator.firstOpenGRComparatorLeaf postSourceComparatorState
    ≡ GRComparator.weakFieldSolverLeaf
postSourceComparatorFirstOpen = refl

postSourceGeometryClosed :
  Geometry.firstOpenGeometryLeaf postSourceGeometryState
    ≡ Geometry.closedGeometry
postSourceGeometryClosed = refl

postSourceEnhancementFirstOpen :
  Enhancement.firstOpenEnhancementLeaf postSourceEnhancementState
    ≡ Enhancement.phaseMatchedFieldLeaf
postSourceEnhancementFirstOpen = refl

------------------------------------------------------------------------
-- Bundle 2: cross the phase boundary while recording the external probe.
------------------------------------------------------------------------

record PhaseProbeBundleReceipt : Set where
  constructor phase-probe-bundle-receipt
  field
    apparatusCarrier : String
    evidenceState : Evidence.EvidenceClosureState
    transitionPaid : Evidence.transitionLocked evidenceState ≡ true
    couplingState : Coupling.AlphaClosureState
    externalProbePaid : Coupling.externalProbeOwned couplingState ≡ true
    phaseControlPaid : Coupling.phaseControlOwned couplingState ≡ true
    enhancementState : Enhancement.EnhancementClosureState
    phaseMatchedFieldPaid : Enhancement.phaseMatchedFieldOwned enhancementState ≡ true

open PhaseProbeBundleReceipt public

data PhaseProbeBundleAuthority : Set where

crossTcCandidateDoesNotCreatePhaseProbeReceipt :
  PhaseProbeBundleAuthority → ⊥
crossTcCandidateDoesNotCreatePhaseProbeReceipt ()

phaseProbeCandidateMove : Choice.InformationMove
phaseProbeCandidateMove = Hyper.crossTcMove

postPhaseEvidenceState : Evidence.EvidenceClosureState
postPhaseEvidenceState =
  Evidence.evidence-closure-state true true true false true false

postPhaseCouplingState : Coupling.AlphaClosureState
postPhaseCouplingState =
  Coupling.alpha-closure-state true true true false false false false

postPhaseEnhancementState : Enhancement.EnhancementClosureState
postPhaseEnhancementState =
  Enhancement.enhancement-closure-state true true true true false false

postPhaseEvidenceFirstOpen :
  Evidence.firstOpenEvidenceLeaf postPhaseEvidenceState
    ≡ Evidence.backgroundClosureLeaf
postPhaseEvidenceFirstOpen = refl

postPhaseCouplingFirstOpen :
  Coupling.firstOpenAlphaLeaf postPhaseCouplingState
    ≡ Coupling.ordinaryGRLeaf
postPhaseCouplingFirstOpen = refl

postPhaseEnhancementFirstOpen :
  Enhancement.firstOpenEnhancementLeaf postPhaseEnhancementState
    ≡ Enhancement.backgroundClosureLeaf
postPhaseEnhancementFirstOpen = refl

------------------------------------------------------------------------
-- Bundle 3: ordinary-model closure on the exact same apparatus.  Weak-field GR
-- is solved from the measured source and ordinary EM/mechanical/thermal
-- backgrounds are closed in the same observable channel.
------------------------------------------------------------------------

record OrdinaryModelClosureBundleReceipt : Set where
  constructor ordinary-model-closure-bundle-receipt
  field
    apparatusCarrier : String
    weakFieldSolverCarrier : String
    backgroundModelCarrier : String

    evidenceState : Evidence.EvidenceClosureState
    evidenceBackgroundsPaid : Evidence.backgroundsClosed evidenceState ≡ true

    couplingState : Coupling.AlphaClosureState
    couplingOrdinaryGRPaid : Coupling.ordinaryGROwned couplingState ≡ true
    couplingBackgroundsPaid : Coupling.ordinaryBackgroundOwned couplingState ≡ true

    comparatorState : GRComparator.GRComparatorState
    comparatorWeakFieldPaid :
      GRComparator.weakFieldPredictionOwned comparatorState ≡ true
    comparatorBackgroundsPaid : GRComparator.backgroundsOwned comparatorState ≡ true

    enhancementState : Enhancement.EnhancementClosureState
    enhancementBackgroundsPaid : Enhancement.backgroundsOwned enhancementState ≡ true

open OrdinaryModelClosureBundleReceipt public

data OrdinaryModelClosureAuthority : Set where

ordinaryModelCandidateDoesNotCreateReceipt :
  OrdinaryModelClosureAuthority → ⊥
ordinaryModelCandidateDoesNotCreateReceipt ()

ordinaryModelClosureMove : Choice.InformationMove
ordinaryModelClosureMove = Choice.informationMove
  Choice.increaseFidelity 3
  "solve same-apparatus weak-field GR and close ordinary EM/mechanical/thermal backgrounds"
  "requires the paid full source/geometry bundle and calibrated nuisance-channel models"
  "same-apparatus ordinary-model closure protocol"

postOrdinaryEvidenceState : Evidence.EvidenceClosureState
postOrdinaryEvidenceState =
  Evidence.evidence-closure-state true true true true true false

postOrdinaryCouplingState : Coupling.AlphaClosureState
postOrdinaryCouplingState =
  Coupling.alpha-closure-state true true true true true false false

postOrdinaryComparatorState : GRComparator.GRComparatorState
postOrdinaryComparatorState =
  GRComparator.gr-comparator-state true true true true true true

postOrdinaryEnhancementState : Enhancement.EnhancementClosureState
postOrdinaryEnhancementState =
  Enhancement.enhancement-closure-state true true true true true false

postOrdinaryEvidenceFirstOpen :
  Evidence.firstOpenEvidenceLeaf postOrdinaryEvidenceState
    ≡ Evidence.constitutiveResidualLeaf
postOrdinaryEvidenceFirstOpen = refl

postOrdinaryCouplingFirstOpen :
  Coupling.firstOpenAlphaLeaf postOrdinaryCouplingState
    ≡ Coupling.reproducibilityLeaf
postOrdinaryCouplingFirstOpen = refl

postOrdinaryComparatorClosed :
  GRComparator.firstOpenGRComparatorLeaf postOrdinaryComparatorState
    ≡ GRComparator.comparatorClosed
postOrdinaryComparatorClosed = refl

postOrdinaryEnhancementFirstOpen :
  Enhancement.firstOpenEnhancementLeaf postOrdinaryEnhancementState
    ≡ Enhancement.constitutiveRatioLeaf
postOrdinaryEnhancementFirstOpen = refl

------------------------------------------------------------------------
-- Bundle 4: independent source-normalised replication plus a declared scaling
-- sweep.  This is the earliest bundle allowed to pay the constitutive/scaling
-- leaves; one repeated anomaly at one operating point is insufficient.
------------------------------------------------------------------------

record ScalingReplicationBundleReceipt : Set where
  constructor scaling-replication-bundle-receipt
  field
    apparatusCarrier : String
    replicationCarrier : String
    scalingSweepCarrier : String

    evidenceState : Evidence.EvidenceClosureState
    evidenceConstitutiveResidualPaid :
      Evidence.constitutiveResidualOwned evidenceState ≡ true

    couplingState : Coupling.AlphaClosureState
    couplingReplicationPaid : Coupling.replicated couplingState ≡ true
    couplingScalingLawPaid : Coupling.scalingLawOwned couplingState ≡ true

    enhancementState : Enhancement.EnhancementClosureState
    enhancementConstitutiveRatioPaid :
      Enhancement.constitutiveRatioOwned enhancementState ≡ true

open ScalingReplicationBundleReceipt public

data ScalingReplicationAuthority : Set where

replicationCandidateDoesNotCreateScalingReceipt :
  ScalingReplicationAuthority → ⊥
replicationCandidateDoesNotCreateScalingReceipt ()

scalingReplicationMove : Choice.InformationMove
scalingReplicationMove = Choice.informationMove
  Choice.replicateMeasurement 4
  "independently replicate the source-normalised residual while sweeping the declared source coordinate"
  "requires reproducibility protocol, same-object source reconstruction, and enough operating points to test residual scaling"
  "replication-plus-scaling protocol"

postScalingEvidenceState : Evidence.EvidenceClosureState
postScalingEvidenceState =
  Evidence.evidence-closure-state true true true true true true

postScalingCouplingState : Coupling.AlphaClosureState
postScalingCouplingState =
  Coupling.alpha-closure-state true true true true true true true

postScalingEnhancementState : Enhancement.EnhancementClosureState
postScalingEnhancementState =
  Enhancement.enhancement-closure-state true true true true true true

postScalingEvidenceBounded :
  Evidence.firstOpenEvidenceLeaf postScalingEvidenceState
    ≡ Evidence.boundedNoPromotionLeaf
postScalingEvidenceBounded = refl

postScalingCouplingClosed :
  Coupling.firstOpenAlphaLeaf postScalingCouplingState ≡ Coupling.alphaClosed
postScalingCouplingClosed = refl

postScalingEnhancementClosed :
  Enhancement.firstOpenEnhancementLeaf postScalingEnhancementState
    ≡ Enhancement.closedEnhancementSplit
postScalingEnhancementClosed = refl

------------------------------------------------------------------------
-- The optimized experimental schedule.  The order is dependency-driven, not a
-- claim that these declared numeric costs are an empirical optimum.
------------------------------------------------------------------------

optimizedExperimentalMoves : List Choice.InformationMove
optimizedExperimentalMoves =
  sourceBundleCandidateMove ∷
  phaseProbeCandidateMove ∷
  ordinaryModelClosureMove ∷
  scalingReplicationMove ∷ []

record OptimizedAcquisitionBoundary : Set where
  constructor optimized-acquisition-boundary
  field
    overlappingSourceLeavesShouldBePaidIndependentlyByDefault : Bool
    oneRichSameApparatusBundleMayPaySeveralSourceLeaves : Bool
    candidateProtocolAutomaticallyCreatesReceipt : Bool
    fullSourceBundleCanCloseLiteralGeometryPlanningState : Bool
    phaseProbeBundleMayAttackThreeConsumerFamilies : Bool
    phaseProbeCandidateAutomaticallyPaysThoseConsumers : Bool
    ordinaryModelBundleMayCloseGRAndBackgroundConsumersTogether : Bool
    singleAnomalyPointDefinesScalingLaw : Bool
    scalingReplicationMayCloseExperimentalCouplingCut : Bool
    closedExperimentalCouplingCutAutomaticallyProvesAntigravity : Bool
    closedExperimentalCouplingCutMayAdvanceToAttributedTheoryComparison : Bool

canonicalOptimizedAcquisitionBoundary : OptimizedAcquisitionBoundary
canonicalOptimizedAcquisitionBoundary =
  optimized-acquisition-boundary
    false true false true true false true false true false true
