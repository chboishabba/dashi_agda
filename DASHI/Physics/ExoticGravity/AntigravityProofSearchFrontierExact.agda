module DASHI.Physics.ExoticGravity.AntigravityProofSearchFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Physics.ExoticGravity.SuperconductingGravityExperimentSearchHypergraphExact as Hyper
import DASHI.Physics.ExoticGravity.SuperconductingSourceConstitutiveEvidenceBidiExact as Evidence
import DASHI.Physics.ExoticGravity.SuperconductingGravityCouplingResidualBidiExact as Coupling
import DASHI.Physics.ExoticGravity.LiTorrStandardGRComparatorBidiExact as GRComparator
import DASHI.Physics.ExoticGravity.LiTorrGeometryAcquisitionBidiExact as Geometry
import DASHI.Physics.ExoticGravity.AntigravityUnificationInteractionExact as Unified

------------------------------------------------------------------------
-- ANTIGRAVITY PROOF-SEARCH FRONTIER
--
-- Keep the independent state machines independent.  Evidence closure,
-- coupling-coefficient closure, same-apparatus GR comparison and literal
-- geometry closure are different consumers.  No one frontier silently pays
-- another.
------------------------------------------------------------------------

data AntigravitySearchResidual : Set where
  sourceCharacterisationResidual : AntigravitySearchResidual
  transitionLockResidual : AntigravitySearchResidual
  externalProbeResidual : AntigravitySearchResidual
  backgroundClosureResidual : AntigravitySearchResidual
  replicationResidual : AntigravitySearchResidual
  constitutiveResidual : AntigravitySearchResidual
  couplingStateWeldResidual : AntigravitySearchResidual
  ordinaryGRComparatorResidual : AntigravitySearchResidual
  scalingLawResidual : AntigravitySearchResidual
  theoryComparisonResidual : AntigravitySearchResidual

residualForEvidenceLeaf : Evidence.EvidenceLeaf → AntigravitySearchResidual
residualForEvidenceLeaf Evidence.sourceCharacterisationLeaf = sourceCharacterisationResidual
residualForEvidenceLeaf Evidence.transitionLockLeaf = transitionLockResidual
residualForEvidenceLeaf Evidence.externalProbeLeaf = externalProbeResidual
residualForEvidenceLeaf Evidence.backgroundClosureLeaf = backgroundClosureResidual
residualForEvidenceLeaf Evidence.replicationLeaf = replicationResidual
residualForEvidenceLeaf Evidence.constitutiveResidualLeaf = constitutiveResidual
residualForEvidenceLeaf Evidence.boundedNoPromotionLeaf = couplingStateWeldResidual

------------------------------------------------------------------------
-- Exact current independent frontiers.
------------------------------------------------------------------------

currentEvidenceLeafIsSourceCharacterisation :
  Evidence.currentFirstOpenEvidenceLeaf ≡ Evidence.sourceCharacterisationLeaf
currentEvidenceLeafIsSourceCharacterisation = refl

currentCouplingLeafIsSourceObservable :
  Coupling.currentFirstOpenAlphaLeaf ≡ Coupling.sourceObservableLeaf
currentCouplingLeafIsSourceObservable = refl

currentGRComparatorLeafIsGeometry :
  GRComparator.currentFirstOpenGRComparatorLeaf ≡ GRComparator.apparatusGeometryLeaf
currentGRComparatorLeafIsGeometry = refl

currentGeometryLeafIsSourceShape :
  Geometry.currentFirstOpenGeometryLeaf ≡ Geometry.sourceShapeLeaf
currentGeometryLeafIsSourceShape = refl

currentAntigravityResidual : AntigravitySearchResidual
currentAntigravityResidual = residualForEvidenceLeaf Evidence.currentFirstOpenEvidenceLeaf

currentResidualIsSourceCharacterisation :
  currentAntigravityResidual ≡ sourceCharacterisationResidual
currentResidualIsSourceCharacterisation = refl

------------------------------------------------------------------------
-- The coarse source-characterisation evidence leaf refines to an AND-cut in
-- the existing hypergraph: source current plus source stress-energy.
------------------------------------------------------------------------

sourceCharacterisationHypergraphCut : List Hyper.SearchState
sourceCharacterisationHypergraphCut =
  Hyper.sourceCurrentLeaf ∷ Hyper.sourceStressEnergyLeaf ∷ []

record CurrentSourceCharacterisationDemand : Set where
  constructor current-source-characterisation-demand
  field
    currentResidual : AntigravitySearchResidual
    currentResidualMatches : currentResidual ≡ currentAntigravityResidual
    requiredHypergraphLeaves : List Hyper.SearchState
    requiredHypergraphLeavesMatch :
      requiredHypergraphLeaves ≡ sourceCharacterisationHypergraphCut
    selectedMove : Choice.InformationMove
    selectedMoveMatches : selectedMove ≡ Hyper.characteriseSourceMove

open CurrentSourceCharacterisationDemand public

canonicalCurrentSourceCharacterisationDemand : CurrentSourceCharacterisationDemand
canonicalCurrentSourceCharacterisationDemand =
  current-source-characterisation-demand
    sourceCharacterisationResidual refl
    sourceCharacterisationHypergraphCut refl
    Hyper.characteriseSourceMove refl

------------------------------------------------------------------------
-- Introspective skip proofs: external-probe ownership and replication are
-- already true in the current EvidenceClosureState, so neither is first there.
-- This says nothing about similarly named coordinates in another state machine.
------------------------------------------------------------------------

externalProbeIsNotCurrentEvidenceLeaf :
  Evidence.currentFirstOpenEvidenceLeaf ≡ Evidence.externalProbeLeaf → ⊥
externalProbeIsNotCurrentEvidenceLeaf ()

replicationIsNotCurrentEvidenceLeaf :
  Evidence.currentFirstOpenEvidenceLeaf ≡ Evidence.replicationLeaf → ⊥
replicationIsNotCurrentEvidenceLeaf ()

------------------------------------------------------------------------
-- Counterfactual recomputation inside the evidence state machine only.
------------------------------------------------------------------------

afterSourceCharacterisation : Evidence.EvidenceClosureState
afterSourceCharacterisation =
  Evidence.evidence-closure-state true false true false true false

afterSourceFirstOpen :
  Evidence.firstOpenEvidenceLeaf afterSourceCharacterisation
    ≡ Evidence.transitionLockLeaf
afterSourceFirstOpen = refl

afterTransitionLock : Evidence.EvidenceClosureState
afterTransitionLock =
  Evidence.evidence-closure-state true true true false true false

afterTransitionFirstOpen :
  Evidence.firstOpenEvidenceLeaf afterTransitionLock
    ≡ Evidence.backgroundClosureLeaf
afterTransitionFirstOpen = refl

afterBackgroundClosure : Evidence.EvidenceClosureState
afterBackgroundClosure =
  Evidence.evidence-closure-state true true true true true false

afterBackgroundFirstOpen :
  Evidence.firstOpenEvidenceLeaf afterBackgroundClosure
    ≡ Evidence.constitutiveResidualLeaf
afterBackgroundFirstOpen = refl

afterConstitutiveResidual : Evidence.EvidenceClosureState
afterConstitutiveResidual =
  Evidence.evidence-closure-state true true true true true true

afterConstitutiveFirstOpen :
  Evidence.firstOpenEvidenceLeaf afterConstitutiveResidual
    ≡ Evidence.boundedNoPromotionLeaf
afterConstitutiveFirstOpen = refl

sourceCharacterisationMove : Choice.InformationMove
sourceCharacterisationMove = Hyper.characteriseSourceMove

transitionLockMove : Choice.InformationMove
transitionLockMove = Hyper.crossTcMove

backgroundClosureMove : Choice.InformationMove
backgroundClosureMove = Hyper.closeBackgroundMove

constitutiveResidualMove : Choice.InformationMove
constitutiveResidualMove = Choice.informationMove
  Choice.takeMeasurement 4
  "compute the same-apparatus source-normalised constitutive residual"
  "requires paid source-characterisation, transition-lock, external-probe, background-closure and replication receipts"
  "consumer-bound constitutive-residual calculation on the exact completed apparatus state"

shortestEvidenceClosureMoves : List Choice.InformationMove
shortestEvidenceClosureMoves =
  sourceCharacterisationMove ∷
  transitionLockMove ∷
  backgroundClosureMove ∷
  constitutiveResidualMove ∷ []

------------------------------------------------------------------------
-- Critical correction: bounded evidence closure is not coupling-alpha closure.
-- The coupling state has extra coordinates, notably ordinary GR and a scaling
-- law.  There is no definition in the imported owners equating
-- constitutiveResidualOwned with scalingLawOwned or supplying ordinaryGROwned.
------------------------------------------------------------------------

data PostEvidenceWorld : Set where
  couplingStillOpen couplingClosed : PostEvidenceWorld

postEvidenceObservation : PostEvidenceWorld → Evidence.EvidenceClosureState
postEvidenceObservation _ = afterConstitutiveResidual

postEvidenceAlphaState : PostEvidenceWorld → Coupling.AlphaClosureState
postEvidenceAlphaState couplingStillOpen =
  Coupling.alpha-closure-state true true true false true true false
postEvidenceAlphaState couplingClosed =
  Coupling.alpha-closure-state true true true true true true true

boundedEvidenceCollision :
  postEvidenceObservation couplingStillOpen ≡ postEvidenceObservation couplingClosed
boundedEvidenceCollision = refl

postEvidenceCouplingDecisionDistinct :
  Coupling.firstOpenAlphaLeaf (postEvidenceAlphaState couplingStillOpen)
    ≡ Coupling.firstOpenAlphaLeaf (postEvidenceAlphaState couplingClosed) → ⊥
postEvidenceCouplingDecisionDistinct ()

boundedEvidenceDoesNotDetermineCouplingClosure : AntigravitySearchResidual
boundedEvidenceDoesNotDetermineCouplingClosure = couplingStateWeldResidual

------------------------------------------------------------------------
-- Multi-consumer shared-source cut.  All four imported owners currently point
-- at source/apparatus characterisation, but a candidate acquisition does not
-- pay all four merely because its prose mentions geometry and stress-energy.
------------------------------------------------------------------------

record SharedSourceAcquisitionReceipt : Set where
  constructor shared-source-acquisition-receipt
  field
    apparatusCarrier : String
    evidenceCarrier : String
    couplingCarrier : String
    grComparatorCarrier : String
    geometryCarrier : String
    evidenceCarrierMatches : evidenceCarrier ≡ apparatusCarrier
    couplingCarrierMatches : couplingCarrier ≡ apparatusCarrier
    grComparatorCarrierMatches : grComparatorCarrier ≡ apparatusCarrier
    geometryCarrierMatches : geometryCarrier ≡ apparatusCarrier

    evidenceState : Evidence.EvidenceClosureState
    evidenceSourcePaid : Evidence.sourceCharacterised evidenceState ≡ true

    couplingState : Coupling.AlphaClosureState
    couplingSourcePaid : Coupling.sourceObservableOwned couplingState ≡ true

    grComparatorState : GRComparator.GRComparatorState
    grGeometryPaid : GRComparator.geometryOwned grComparatorState ≡ true

    geometryState : Geometry.GeometryClosureState
    sourceShapePaid : Geometry.sourceShapeOwned geometryState ≡ true

open SharedSourceAcquisitionReceipt public

data SharedSourceReceiptAuthority : Set where

candidateMoveDoesNotManufactureSharedReceipt :
  SharedSourceReceiptAuthority → ⊥
candidateMoveDoesNotManufactureSharedReceipt ()

------------------------------------------------------------------------
-- Even after the evidence cut, theory comparison is downstream of a coupling
-- weld / ordinary-GR / scaling-law frontier.  Observation-route type remains
-- relevant but does not skip those coordinates.
------------------------------------------------------------------------

postCouplingRoute : Unified.ClaimObservationRoute → AntigravitySearchResidual
postCouplingRoute (Unified.gravitationalObservationRoute channel) = theoryComparisonResidual
postCouplingRoute Unified.inertialComparisonRoute = theoryComparisonResidual
postCouplingRoute Unified.ordinaryMomentumClosureRoute = theoryComparisonResidual

record AntigravityProofSearchBoundary : Set where
  constructor antigravity-proof-search-boundary
  field
    currentFirstEvidenceResidualIsSourceCharacterisation : Bool
    currentCouplingResidualIsSourceObservable : Bool
    currentGRComparatorResidualIsGeometry : Bool
    currentLiteralGeometryResidualIsSourceShape : Bool
    sourceCharacterisationIsSingleScalarLeaf : Bool
    alreadyOwnedEvidenceLeavesMayBeSkippedInsideEvidenceState : Bool
    completedEvidenceCutAutomaticallyClosesCouplingAlpha : Bool
    constitutiveResidualAutomaticallyEqualsScalingLaw : Bool
    completedEvidenceCutAutomaticallySuppliesOrdinaryGR : Bool
    sharedSourceCandidateMoveAutomaticallyPaysAllConsumers : Bool
    explicitSameApparatusReceiptRequiredForSharedPayment : Bool
    completedCouplingCutAutomaticallyProvesAntigravity : Bool
    rawExperimentalFindingAutomaticallyClosesKernelProof : Bool

canonicalAntigravityProofSearchBoundary : AntigravityProofSearchBoundary
canonicalAntigravityProofSearchBoundary =
  antigravity-proof-search-boundary
    true true true true false true false false false false true false false
