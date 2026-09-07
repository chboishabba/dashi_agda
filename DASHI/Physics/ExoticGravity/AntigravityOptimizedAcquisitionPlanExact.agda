module DASHI.Physics.ExoticGravity.AntigravityOptimizedAcquisitionPlanExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
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
-- Proof search should acquire a sufficiently rich source/geometry bundle once
-- rather than paying overlapping first leaves independently.  This module
-- describes the payment target.  It does not construct an empirical receipt.
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

------------------------------------------------------------------------
-- Exact hypothetical post-payment frontier.  These states say what would be
-- true if a real FullSourceGeometryBundleReceipt were obtained while retaining
-- already-owned EvidenceClosureState coordinates.  They are planning fixtures,
-- not claims about current experiments.
------------------------------------------------------------------------

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
-- Second optimized bundle: cross phase while recording the external probe.
-- This can potentially attack transition-lock, coupling external-probe/phase,
-- and enhancement phase-matched-field coordinates together, but only with a
-- receipt that proves those exact payments on the same apparatus.
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
-- After the first two optimized bundles the dominant remaining collision is
-- now ordinary-model closure: weak-field GR plus ordinary backgrounds.  This is
-- much narrower than a generic search for anomalous force.
------------------------------------------------------------------------

record OptimizedAcquisitionBoundary : Set where
  constructor optimized-acquisition-boundary
  field
    overlappingSourceLeavesShouldBePaidIndependentlyByDefault : Bool
    oneRichSameApparatusBundleMayPaySeveralSourceLeaves : Bool
    candidateProtocolAutomaticallyCreatesReceipt : Bool
    fullSourceBundleCanCloseLiteralGeometryPlanningState : Bool
    phaseProbeBundleMayAttackThreeConsumerFamilies : Bool
    phaseProbeCandidateAutomaticallyPaysThoseConsumers : Bool
    afterTwoBundlesOrdinaryModelClosureIsDominant : Bool
    optimizedPlanAutomaticallyProvesAntigravity : Bool

canonicalOptimizedAcquisitionBoundary : OptimizedAcquisitionBoundary
canonicalOptimizedAcquisitionBoundary =
  optimized-acquisition-boundary
    false true false true true false true false
