module DASHI.Core.HistoryQualifiedSelectionTopologyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.EpistemicSuspensionExact as Suspension

------------------------------------------------------------------------
-- HISTORY-QUALIFIED ACCESS AND SELECTION TOPOLOGY
--
-- This owner specialises the existing history-conditioned/fabric machinery to
-- sequential contingent selection.  The motivating examples include heats,
-- brackets, round-robin tournaments, staged review, proof-route admission and
-- governance escalation.  The finite witnesses below are synthetic DASHI
-- constructions; they are not empirical claims about any particular sport,
-- market, institution or historical case.
--
-- Central separations:
--
--   present participant identity != qualification history
--   nominal node existence       != history-qualified accessibility
--   same opponent identity       != same opponent history
--   same candidate field         != same selected frontier under every topology
--   shared historical root       != inherited admissibility
--   unresolved gate              != reject != accept
------------------------------------------------------------------------

record HistoryQualifiedSelectionSystem : Set₁ where
  field
    Participant History Node OpponentHistory Outcome Topology FrontierCode : Set

    historyOf : Participant → History
    canAccess : Node → History → Set
    interact : Participant → OpponentHistory → Outcome
    frontier : Topology → FrontierCode

    reading : String

open HistoryQualifiedSelectionSystem public

record QualifiedEntry
    (system : HistoryQualifiedSelectionSystem)
    (node : Node system)
    (participant : Participant system) : Set where
  constructor qualified-entry
  field
    qualificationWitness : canAccess system node (historyOf system participant)

open QualifiedEntry public

------------------------------------------------------------------------
-- Finals-style history qualification.
------------------------------------------------------------------------

data HeatHistory : Set where
  eliminated pending qualified : HeatHistory

data FinalNode : Set where
  finals : FinalNode

finalAccess : FinalNode → HeatHistory → Set
finalAccess finals eliminated = ⊥
finalAccess finals pending = ⊥
finalAccess finals qualified = ⊤

qualifiedCanEnterFinal : finalAccess finals qualified
qualifiedCanEnterFinal = tt

eliminatedCannotEnterFinal : finalAccess finals eliminated → ⊥
eliminatedCannotEnterFinal impossible = impossible

pendingCannotEnterFinal : finalAccess finals pending → ⊥
pendingCannotEnterFinal impossible = impossible

------------------------------------------------------------------------
-- The ternary gate keeps unresolved history distinct from failure/success.
------------------------------------------------------------------------

historyEvidence : HeatHistory → Suspension.TernaryEvidence
historyEvidence eliminated = Suspension.negativeEvidence
historyEvidence pending = Suspension.neutralEvidence
historyEvidence qualified = Suspension.positiveEvidence

pendingMeansRefine :
  Suspension.disposition (historyEvidence pending)
  ≡ Suspension.suspendAndRefine
pendingMeansRefine = refl

eliminatedMeansReject :
  Suspension.disposition (historyEvidence eliminated)
  ≡ Suspension.rejectHere
eliminatedMeansReject = refl

qualifiedMeansAccept :
  Suspension.disposition (historyEvidence qualified)
  ≡ Suspension.acceptHere
qualifiedMeansAccept = refl

------------------------------------------------------------------------
-- Opponent history can alter an interaction while nominal opponent identity is
-- held fixed.  This is the tournament analogue of relational-history fibres.
------------------------------------------------------------------------

data Competitor : Set where
  alpha beta : Competitor

data OpponentIdentity : Set where
  sameOpponent : OpponentIdentity

data OpponentPath : Set where
  freshPath depletedPath : OpponentPath

data MatchOutcome : Set where
  advances eliminatedOutcome : MatchOutcome

opponentIdentity : OpponentPath → OpponentIdentity
opponentIdentity _ = sameOpponent

alphaOutcome : OpponentPath → MatchOutcome
alphaOutcome freshPath = eliminatedOutcome
alphaOutcome depletedPath = advances

sameOpponentProjection :
  opponentIdentity freshPath ≡ opponentIdentity depletedPath
sameOpponentProjection = refl

opponentHistoryChangesOutcome :
  alphaOutcome freshPath ≡ alphaOutcome depletedPath → ⊥
opponentHistoryChangesOutcome ()

opponentHistoryOutcomeWitness :
  INF.NonFactorabilityWitness opponentIdentity alphaOutcome
opponentHistoryOutcomeWitness =
  INF.nonFactorabilityWitness
    freshPath
    depletedPath
    sameOpponentProjection
    opponentHistoryChangesOutcome

opponentIdentityCannotRecoverInteractionOutcome :
  INF.FactorsThrough opponentIdentity alphaOutcome → ⊥
opponentIdentityCannotRecoverInteractionOutcome =
  INF.witnessRulesOutEveryFlatFactorisation opponentHistoryOutcomeWitness

------------------------------------------------------------------------
-- Selection topology matters even when the nominal candidate field is fixed.
------------------------------------------------------------------------

data TournamentTopology : Set where
  bracket roundRobin : TournamentTopology

data CandidateField : Set where
  sameField : CandidateField

data Frontier : Set where
  alphaFrontier betaFrontier : Frontier

fieldOf : TournamentTopology → CandidateField
fieldOf _ = sameField

selectedFrontier : TournamentTopology → Frontier
selectedFrontier bracket = alphaFrontier
selectedFrontier roundRobin = betaFrontier

sameCandidateField : fieldOf bracket ≡ fieldOf roundRobin
sameCandidateField = refl

differentTopologyDifferentFrontier :
  selectedFrontier bracket ≡ selectedFrontier roundRobin → ⊥
differentTopologyDifferentFrontier ()

topologySelectionWitness :
  INF.NonFactorabilityWitness fieldOf selectedFrontier
topologySelectionWitness =
  INF.nonFactorabilityWitness
    bracket
    roundRobin
    sameCandidateField
    differentTopologyDifferentFrontier

candidateFieldCannotRecoverSelectedFrontier :
  INF.FactorsThrough fieldOf selectedFrontier → ⊥
candidateFieldCannotRecoverSelectedFrontier =
  INF.witnessRulesOutEveryFlatFactorisation topologySelectionWitness

------------------------------------------------------------------------
-- Filter order can itself be substantive when filters do not commute.
------------------------------------------------------------------------

data FilterState : Set where
  initial
  rightsFirst
  profitFirst
  rightsThenProfit
  profitThenRights
  : FilterState

rightsFilter : FilterState → FilterState
rightsFilter initial = rightsFirst
rightsFilter profitFirst = profitThenRights
rightsFilter state = state

profitFilter : FilterState → FilterState
profitFilter initial = profitFirst
profitFilter rightsFirst = rightsThenProfit
profitFilter state = state

filterOrderNoncommutes :
  profitFilter (rightsFilter initial)
  ≡ rightsFilter (profitFilter initial) → ⊥
filterOrderNoncommutes ()

------------------------------------------------------------------------
-- Hierarchical/p-adic-style shared-root proximity is a candidate relation, not
-- permission transport.  The finite object deliberately avoids claiming a
-- metric theorem: it captures only the reusable governance boundary that two
-- histories can share a root while diverging at an admission-critical leaf.
------------------------------------------------------------------------

data RootedHistory : Set where
  sameRootAdmitted sameRootBlocked : RootedHistory

data SharedRootCode : Set where
  commonRoot : SharedRootCode

data AdmissionClass : Set where
  admittedClass blockedClass : AdmissionClass

sharedRoot : RootedHistory → SharedRootCode
sharedRoot _ = commonRoot

admissionClass : RootedHistory → AdmissionClass
admissionClass sameRootAdmitted = admittedClass
admissionClass sameRootBlocked = blockedClass

sameRootCollision :
  sharedRoot sameRootAdmitted ≡ sharedRoot sameRootBlocked
sameRootCollision = refl

admissionDiffersUnderSameRoot :
  admissionClass sameRootAdmitted ≡ admissionClass sameRootBlocked → ⊥
admissionDiffersUnderSameRoot ()

sharedRootAdmissionWitness :
  INF.NonFactorabilityWitness sharedRoot admissionClass
sharedRootAdmissionWitness =
  INF.nonFactorabilityWitness
    sameRootAdmitted
    sameRootBlocked
    sameRootCollision
    admissionDiffersUnderSameRoot

sharedRootCannotRecoverAdmission :
  INF.FactorsThrough sharedRoot admissionClass → ⊥
sharedRootCannotRecoverAdmission =
  INF.witnessRulesOutEveryFlatFactorisation sharedRootAdmissionWitness

------------------------------------------------------------------------
-- Scope / source boundary.
------------------------------------------------------------------------

record HistoryQualifiedSelectionBoundary : Set where
  constructor history-qualified-selection-boundary
  field
    nodeExistsMeansEveryoneMayEnter : Bool
    nodeExistsMeansEveryoneMayEnterIsFalse :
      nodeExistsMeansEveryoneMayEnter ≡ false
    sameOpponentMeansSameInteraction : Bool
    sameOpponentMeansSameInteractionIsFalse :
      sameOpponentMeansSameInteraction ≡ false
    sameFieldMeansSameFrontier : Bool
    sameFieldMeansSameFrontierIsFalse :
      sameFieldMeansSameFrontier ≡ false
    filterOrderIsAlwaysTrivial : Bool
    filterOrderIsAlwaysTrivialIsFalse :
      filterOrderIsAlwaysTrivial ≡ false
    sharedRootMeansAdmissionTransports : Bool
    sharedRootMeansAdmissionTransportsIsFalse :
      sharedRootMeansAdmissionTransports ≡ false
    neutralGateMeansReject : Bool
    neutralGateMeansRejectIsFalse : neutralGateMeansReject ≡ false
    finiteTournamentWitnessIsEmpiricalSportsClaim : Bool
    finiteTournamentWitnessIsEmpiricalSportsClaimIsFalse :
      finiteTournamentWitnessIsEmpiricalSportsClaim ≡ false

canonicalHistoryQualifiedSelectionBoundary : HistoryQualifiedSelectionBoundary
canonicalHistoryQualifiedSelectionBoundary =
  history-qualified-selection-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
