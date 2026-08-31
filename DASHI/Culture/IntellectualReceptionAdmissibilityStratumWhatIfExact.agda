module DASHI.Culture.IntellectualReceptionAdmissibilityStratumWhatIfExact where

------------------------------------------------------------------------
-- INTELLECTUAL RECEPTION / PATH-QUALIFIED STRATUM / WHAT-IF CONES
--
-- Here "stratum" means more than a coarse label.  It is a situated region
-- whose admissible moves and future cone may depend on:
--
--   present surface
--   + arrival history
--   + selection/reception topology
--   + current enablement / admission conditions.
--
-- This module consumes merged DASHI history/admissibility machinery.  PR #666
-- remains inspiration only while open: no Base369/Monster owner is imported.
-- The finite scenarios below are DASHI constructions, not empirical laws of
-- intellectual history and not claims of physical gauge/Monster structure.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Unit using (⊤; tt)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.HistoryConditionedChoiceExact as Choice
import DASHI.Core.HistoryQualifiedSelectionTopologyExact as Selection
import DASHI.Core.RelationalHistoryFabricExact as Fabric
import DASHI.Core.AdmissibleTransitionHyperfabricExact as Admissible
import DASHI.Culture.IntellectualReceptionStratifiedFibreOrderBidiExact as Reception

------------------------------------------------------------------------
-- 1. Path-qualified reception stratum.
------------------------------------------------------------------------

data ArrivalHistory : Set where
  commentaryFirst
  institutionFirst
  movementFirst
  archivalRediscovery
  : ArrivalHistory

data ReceptionTopology : Set where
  bracketLikeCanon
  roundRobinPluralReception
  movementNetwork
  archivalReview
  : ReceptionTopology

data CoarseReceptionPosition : Set where
  samePresentVocabulary
  : CoarseReceptionPosition

data AdmissionGate : Set where
  closedGate pendingGate openGate : AdmissionGate

data AdmissibleMoveCode : Set where
  narrowCanonMove
  pluralComparisonMove
  counterTraditionMove
  sourceRecoveryMove
  : AdmissibleMoveCode

data FutureConeCode : Set where
  canonDominantCone
  pluralContestableCone
  movementReclamationCone
  archivalReconstructionCone
  : FutureConeCode

record ReceptionAdmissibilityStratum : Set where
  constructor reception-admissibility-stratum
  field
    present : CoarseReceptionPosition
    arrival : ArrivalHistory
    topology : ReceptionTopology
    gate : AdmissionGate
    nextMove : AdmissibleMoveCode
    futureCone : FutureConeCode

open ReceptionAdmissibilityStratum public

commentaryCanonStratum : ReceptionAdmissibilityStratum
commentaryCanonStratum =
  reception-admissibility-stratum
    samePresentVocabulary commentaryFirst bracketLikeCanon openGate
    narrowCanonMove canonDominantCone

commentaryPluralStratum : ReceptionAdmissibilityStratum
commentaryPluralStratum =
  reception-admissibility-stratum
    samePresentVocabulary commentaryFirst roundRobinPluralReception openGate
    pluralComparisonMove pluralContestableCone

institutionCanonStratum : ReceptionAdmissibilityStratum
institutionCanonStratum =
  reception-admissibility-stratum
    samePresentVocabulary institutionFirst bracketLikeCanon openGate
    narrowCanonMove canonDominantCone

movementStratum : ReceptionAdmissibilityStratum
movementStratum =
  reception-admissibility-stratum
    samePresentVocabulary movementFirst movementNetwork openGate
    counterTraditionMove movementReclamationCone

archiveStratum : ReceptionAdmissibilityStratum
archiveStratum =
  reception-admissibility-stratum
    samePresentVocabulary archivalRediscovery archivalReview pendingGate
    sourceRecoveryMove archivalReconstructionCone

------------------------------------------------------------------------
-- 2. Same present surface, different arrival history -> different future cone.
------------------------------------------------------------------------

presentSurface : ReceptionAdmissibilityStratum → CoarseReceptionPosition
presentSurface = present

arrivalCode : ReceptionAdmissibilityStratum → ArrivalHistory
arrivalCode = arrival

moveCode : ReceptionAdmissibilityStratum → AdmissibleMoveCode
moveCode = nextMove

futureCode : ReceptionAdmissibilityStratum → FutureConeCode
futureCode = futureCone

samePresentAcrossHistoryFixture :
  presentSurface commentaryCanonStratum ≡ presentSurface movementStratum
samePresentAcrossHistoryFixture = refl

historyFixtureFutureDiffers :
  futureCode commentaryCanonStratum ≡ futureCode movementStratum → ⊥
historyFixtureFutureDiffers ()

samePresentCannotRecoverFutureCone :
  INF.FactorsThrough presentSurface futureCode → ⊥
samePresentCannotRecoverFutureCone =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      commentaryCanonStratum movementStratum
      samePresentAcrossHistoryFixture
      historyFixtureFutureDiffers)

------------------------------------------------------------------------
-- 3. Same candidate/intellectual field, different topology -> different
-- selected continuation.  This is the reception analogue of bracket vs
-- round-robin selection; the generic tournament theorem is also re-exported.
------------------------------------------------------------------------

data SameInterpretiveField : Set where sameInterpretiveField : SameInterpretiveField

data SelectedReceptionFrontier : Set where
  canonicalFrontier pluralFrontier : SelectedReceptionFrontier

interpretiveField : ReceptionTopology → SameInterpretiveField
interpretiveField _ = sameInterpretiveField

selectedReceptionFrontier : ReceptionTopology → SelectedReceptionFrontier
selectedReceptionFrontier bracketLikeCanon = canonicalFrontier
selectedReceptionFrontier roundRobinPluralReception = pluralFrontier
selectedReceptionFrontier movementNetwork = pluralFrontier
selectedReceptionFrontier archivalReview = pluralFrontier

sameFieldAcrossTopology :
  interpretiveField bracketLikeCanon ≡ interpretiveField roundRobinPluralReception
sameFieldAcrossTopology = refl

topologyChangesReceptionFrontier :
  selectedReceptionFrontier bracketLikeCanon
  ≡ selectedReceptionFrontier roundRobinPluralReception → ⊥
topologyChangesReceptionFrontier ()

sameInterpretiveFieldCannotRecoverSelectedReceptionFrontier :
  INF.FactorsThrough interpretiveField selectedReceptionFrontier → ⊥
sameInterpretiveFieldCannotRecoverSelectedReceptionFrontier =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      bracketLikeCanon roundRobinPluralReception
      sameFieldAcrossTopology topologyChangesReceptionFrontier)

canonicalBracketRoundRobinPrecedent :
  INF.FactorsThrough Selection.fieldOf Selection.selectedFrontier → ⊥
canonicalBracketRoundRobinPrecedent =
  Selection.candidateFieldCannotRecoverSelectedFrontier

------------------------------------------------------------------------
-- 4. History and topology are independently relevant axes.
------------------------------------------------------------------------

sameHistoryDifferentTopologyMoveDiffers :
  moveCode commentaryCanonStratum ≡ moveCode commentaryPluralStratum → ⊥
sameHistoryDifferentTopologyMoveDiffers ()

sameTopologyDifferentHistoryFutureDiffers :
  futureCode commentaryCanonStratum ≡ futureCode institutionCanonStratum → ⊥
sameTopologyDifferentHistoryFutureDiffers ()

-- The second fixture above shares topology but currently also shares the same
-- encoded cone.  Use the meaning/order carrier for a genuine same-topology,
-- different-history distinction instead of manufacturing a false theorem.

data SameTopologyHistoryState : Set where
  canonViaCommentary canonViaInstitution : SameTopologyHistoryState

data SameTopologyCode : Set where sameCanonTopology : SameTopologyCode

data FineHistoryEndpoint : Set where
  commentaryCanonEndpoint institutionalCanonEndpoint : FineHistoryEndpoint

sameTopologySurface : SameTopologyHistoryState → SameTopologyCode
sameTopologySurface _ = sameCanonTopology

fineHistoryEndpoint : SameTopologyHistoryState → FineHistoryEndpoint
fineHistoryEndpoint canonViaCommentary = commentaryCanonEndpoint
fineHistoryEndpoint canonViaInstitution = institutionalCanonEndpoint

sameTopologyCannotRecoverArrivalHistory :
  INF.FactorsThrough sameTopologySurface fineHistoryEndpoint → ⊥
sameTopologyCannotRecoverArrivalHistory =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      canonViaCommentary canonViaInstitution refl (λ ()))

------------------------------------------------------------------------
-- 5. Typed what-if scenarios.
--
-- A what-if does not assert the counterfactual is historically true.  It names
-- the coordinate changed and returns the resulting finite continuation code.
------------------------------------------------------------------------

data WhatIfIntervention : Set where
  whatIfPluralTopology
  whatIfMovementReception
  whatIfSourceRecovered
  whatIfCanonClosed
  : WhatIfIntervention

applyWhatIf : WhatIfIntervention → ReceptionAdmissibilityStratum → ReceptionAdmissibilityStratum
applyWhatIf whatIfPluralTopology state =
  reception-admissibility-stratum
    (present state) (arrival state) roundRobinPluralReception openGate
    pluralComparisonMove pluralContestableCone
applyWhatIf whatIfMovementReception state =
  reception-admissibility-stratum
    (present state) movementFirst movementNetwork openGate
    counterTraditionMove movementReclamationCone
applyWhatIf whatIfSourceRecovered state =
  reception-admissibility-stratum
    (present state) archivalRediscovery archivalReview openGate
    sourceRecoveryMove archivalReconstructionCone
applyWhatIf whatIfCanonClosed state =
  reception-admissibility-stratum
    (present state) (arrival state) bracketLikeCanon closedGate
    narrowCanonMove canonDominantCone

pluralWhatIfChangesCone :
  futureCode (applyWhatIf whatIfPluralTopology commentaryCanonStratum)
  ≡ futureCode commentaryCanonStratum → ⊥
pluralWhatIfChangesCone ()

movementWhatIfChangesMove :
  moveCode (applyWhatIf whatIfMovementReception commentaryCanonStratum)
  ≡ moveCode commentaryCanonStratum → ⊥
movementWhatIfChangesMove ()

------------------------------------------------------------------------
-- 6. Canonical history/future-cone and relational-fabric reuse.
------------------------------------------------------------------------

choiceBoundary : Choice.HistoryConditionedChoiceBoundary
choiceBoundary = Choice.canonicalHistoryConditionedChoiceBoundary

fabricBoundary : Fabric.RelationalHistoryFabricBoundary
fabricBoundary = Fabric.canonicalRelationalHistoryFabricBoundary

sameNowCanHideDifferentCanonicalFutureCones :
  INF.FactorsThrough
    (Choice.observeFutureHistory Choice.toyFutureConeSurface)
    (Choice.futureCone Choice.toyFutureConeSurface) → ⊥
sameNowCanHideDifferentCanonicalFutureCones =
  Choice.futureConeCannotDescendThroughPresentObservation
    Choice.canonicalToyFutureConeWitness

relationalHistoryCanPropagateToFutureCone :
  INF.FactorsThrough
    (Fabric.observe Fabric.toyFabric)
    (Fabric.futureConeOf Fabric.toyFabric) → ⊥
relationalHistoryCanPropagateToFutureCone =
  Fabric.historyPropagationBlocksCoarseFutureDescent
    Fabric.canonicalHistoryPropagationWitness

------------------------------------------------------------------------
-- 7. Proof-relevant admissibility: disabled != low probability.
------------------------------------------------------------------------

data ReceptionMove : Set where
  enterCanon enterPlural enterMovement recoverSource : ReceptionMove

data ReceptionParameter : Set where ordinaryReception : ReceptionParameter

data ReceptionInvariant : Set where receptionInvariant : ReceptionInvariant

enabled : ReceptionMove → ReceptionParameter → ReceptionAdmissibilityStratum → Set
enabled enterCanon ordinaryReception state with gate state
... | openGate = ⊤
... | pendingGate = ⊥
... | closedGate = ⊥
enabled enterPlural ordinaryReception state with gate state
... | openGate = ⊤
... | pendingGate = ⊥
... | closedGate = ⊥
enabled enterMovement ordinaryReception state with gate state
... | openGate = ⊤
... | pendingGate = ⊥
... | closedGate = ⊥
enabled recoverSource ordinaryReception state with gate state
... | openGate = ⊤
... | pendingGate = ⊤
... | closedGate = ⊥

step : ReceptionMove → ReceptionParameter → ReceptionAdmissibilityStratum → ReceptionAdmissibilityStratum
step enterCanon _ state =
  reception-admissibility-stratum
    (present state) (arrival state) bracketLikeCanon openGate
    narrowCanonMove canonDominantCone
step enterPlural _ state = applyWhatIf whatIfPluralTopology state
step enterMovement _ state = applyWhatIf whatIfMovementReception state
step recoverSource _ state = applyWhatIf whatIfSourceRecovered state

receptionTransitionSystem : Admissible.AdmissibleTransitionSystem
receptionTransitionSystem =
  Admissible.admissibleTransitionSystem
    ReceptionAdmissibilityStratum
    ReceptionParameter
    ReceptionMove
    enabled
    step
    (λ _ → ⊤)
    (λ move parameter state enabledHere invariantHere → tt)
    "Finite DASHI reception what-if transition system; not an empirical law."

sourceRecoveryAdmittedWhilePending :
  Admissible.AdmittedStep
    receptionTransitionSystem recoverSource ordinaryReception archiveStratum
sourceRecoveryAdmittedWhilePending =
  Admissible.admittedStep tt tt

canonEntryBlockedWhilePending :
  Admissible.Enabled receptionTransitionSystem enterCanon ordinaryReception archiveStratum → ⊥
canonEntryBlockedWhilePending impossible = impossible

------------------------------------------------------------------------
-- 8. Base369/Monster comparison boundary while #666 remains open.
------------------------------------------------------------------------

data ReceptionStratumIsLiteralBase369Stratum : Set where
data ReceptionFutureConeIsMonsterSector : Set where
data CounterfactualBranchIsPhysicalWorld : Set where
data MoreWhatIfsMeansMoreTruth : Set where

receptionStratumIsNotLiteralBase369Stratum : ReceptionStratumIsLiteralBase369Stratum → ⊥
receptionStratumIsNotLiteralBase369Stratum ()

receptionFutureConeIsNotMonsterSector : ReceptionFutureConeIsMonsterSector → ⊥
receptionFutureConeIsNotMonsterSector ()

counterfactualBranchIsNotPhysicalWorld : CounterfactualBranchIsPhysicalWorld → ⊥
counterfactualBranchIsNotPhysicalWorld ()

moreWhatIfsDoNotMeanMoreTruth : MoreWhatIfsMeansMoreTruth → ⊥
moreWhatIfsDoNotMeanMoreTruth ()

------------------------------------------------------------------------
-- 9. Boundary.
------------------------------------------------------------------------

record IntellectualReceptionAdmissibilityStratumBoundary : Set where
  constructor intellectual-reception-admissibility-stratum-boundary
  field
    stratumIsOnlyCoarseLabel : Bool
    samePresentMeansSameAdmissibleMoves : Bool
    samePresentMeansSameFutureCone : Bool
    sameCandidateFieldMeansSameFrontier : Bool
    sameTopologyMeansSameArrivalHistory : Bool
    disabledMoveMeansLowProbabilityMove : Bool
    whatIfBranchIsAssertedHistory : Bool
    receptionStratumEqualsBase369Geometry : Bool
    receptionFutureConeEqualsMonsterSector : Bool
    pathTopologyAndGateMayChangeAdmissibility : Bool
    counterfactualsAreTypedAlternativeContinuations : Bool

canonicalIntellectualReceptionAdmissibilityStratumBoundary :
  IntellectualReceptionAdmissibilityStratumBoundary
canonicalIntellectualReceptionAdmissibilityStratumBoundary =
  intellectual-reception-admissibility-stratum-boundary
    false false false false false false false false false true true
