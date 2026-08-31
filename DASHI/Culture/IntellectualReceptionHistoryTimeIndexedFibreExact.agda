module DASHI.Culture.IntellectualReceptionHistoryTimeIndexedFibreExact where

------------------------------------------------------------------------
-- INTELLECTUAL RECEPTION / HISTORY-TIME INDEXED FIBRE
--
-- The reception "stratum" is represented here as the fine fibre at a path/time
-- index.  Residue, topology, gate, admissibility and future cone are projections
-- of that fibre.  Equality of selected coarse projections does not imply
-- equality of the underlying fibre.
--
-- "Fibre" is a DASHI carrier concept here.  This module does not claim a
-- geometric/vector bundle, gauge field, Base369 identity or physical spacetime.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.RelationalHistoryFabricExact as Fabric
import DASHI.Culture.IntellectualReceptionAdmissibilityStratumWhatIfExact as Stratum
import DASHI.Culture.IntellectualReceptionMultiResidueAdmissibilityLedgerExact as Ledger
import DASHI.Culture.IntellectualReceptionTemporalMultiResidueAdmissibilityExact as Temporal

------------------------------------------------------------------------
-- 1. The fine fibre itself.
------------------------------------------------------------------------

record HistoryTimeIndexedReceptionFibre : Set where
  constructor history-time-indexed-reception-fibre
  field
    history : Temporal.TemporalReceptionHistory
    time : Temporal.ReceptionTime
    present : Stratum.CoarseReceptionPosition
    residue : Ledger.ReceptionResidueLedger
    topology : Stratum.ReceptionTopology
    gate : Stratum.AdmissionGate
    pluralEnabled : Bool
    movementEnabled : Bool
    authorityEnabled : Bool
    futureCone : Stratum.FutureConeCode

open HistoryTimeIndexedReceptionFibre public

historyTopology : Temporal.TemporalReceptionHistory → Stratum.ReceptionTopology
historyTopology Temporal.closureTemporalHistory = Stratum.bracketLikeCanon
historyTopology Temporal.archiveTemporalHistory = Stratum.archivalReview
historyTopology Temporal.movementEarlyAuthorityHistory = Stratum.movementNetwork
historyTopology Temporal.movementLateAuthorityHistory = Stratum.movementNetwork

historyGate : Temporal.TemporalReceptionHistory → Temporal.ReceptionTime → Stratum.AdmissionGate
historyGate Temporal.closureTemporalHistory Temporal.t0 = Stratum.openGate
historyGate Temporal.closureTemporalHistory Temporal.t1 = Stratum.closedGate
historyGate Temporal.closureTemporalHistory Temporal.t2 = Stratum.closedGate
historyGate Temporal.closureTemporalHistory Temporal.t3 = Stratum.closedGate
historyGate Temporal.archiveTemporalHistory Temporal.t0 = Stratum.openGate
historyGate Temporal.archiveTemporalHistory Temporal.t1 = Stratum.pendingGate
historyGate Temporal.archiveTemporalHistory Temporal.t2 = Stratum.openGate
historyGate Temporal.archiveTemporalHistory Temporal.t3 = Stratum.openGate
historyGate Temporal.movementEarlyAuthorityHistory _ = Stratum.openGate
historyGate Temporal.movementLateAuthorityHistory _ = Stratum.openGate

historyFuture : Temporal.TemporalReceptionHistory → Temporal.ReceptionTime → Stratum.FutureConeCode
historyFuture Temporal.closureTemporalHistory Temporal.t0 = Stratum.canonDominantCone
historyFuture Temporal.closureTemporalHistory Temporal.t1 = Stratum.canonDominantCone
historyFuture Temporal.closureTemporalHistory Temporal.t2 = Stratum.pluralContestableCone
historyFuture Temporal.closureTemporalHistory Temporal.t3 = Stratum.pluralContestableCone
historyFuture Temporal.archiveTemporalHistory Temporal.t0 = Stratum.canonDominantCone
historyFuture Temporal.archiveTemporalHistory Temporal.t1 = Stratum.archivalReconstructionCone
historyFuture Temporal.archiveTemporalHistory Temporal.t2 = Stratum.pluralContestableCone
historyFuture Temporal.archiveTemporalHistory Temporal.t3 = Stratum.pluralContestableCone
historyFuture Temporal.movementEarlyAuthorityHistory _ = Stratum.movementReclamationCone
historyFuture Temporal.movementLateAuthorityHistory _ = Stratum.movementReclamationCone

fibreAt :
  Temporal.TemporalReceptionHistory →
  Temporal.ReceptionTime →
  HistoryTimeIndexedReceptionFibre
fibreAt historyHere timeHere =
  history-time-indexed-reception-fibre
    historyHere
    timeHere
    Stratum.samePresentVocabulary
    (Temporal.ledgerAt historyHere timeHere)
    (historyTopology historyHere)
    (historyGate historyHere timeHere)
    (Temporal.enabledAt historyHere timeHere Temporal.pluralContinuation)
    (Temporal.enabledAt historyHere timeHere Temporal.movementContinuation)
    (Temporal.enabledAt historyHere timeHere Temporal.authorityContinuation)
    (historyFuture historyHere timeHere)

------------------------------------------------------------------------
-- 2. Same time + same present + same future can still hide different fibres.
------------------------------------------------------------------------

data SameTimePresentFutureCase : Set where
  earlyAuthorityAtT1 lateAuthorityAtT1 : SameTimePresentFutureCase

data SameTimePresentFutureCode : Set where
  sameT1PresentMovementFuture : SameTimePresentFutureCode

data FineFibreCode : Set where
  earlyAuthorityFibre lateAuthorityFibre : FineFibreCode

sameTimePresentFuture : SameTimePresentFutureCase → SameTimePresentFutureCode
sameTimePresentFuture _ = sameT1PresentMovementFuture

fineFibreCode : SameTimePresentFutureCase → FineFibreCode
fineFibreCode earlyAuthorityAtT1 = earlyAuthorityFibre
fineFibreCode lateAuthorityAtT1 = lateAuthorityFibre

fineFibreCodesDiffer :
  fineFibreCode earlyAuthorityAtT1 ≡ fineFibreCode lateAuthorityAtT1 → ⊥
fineFibreCodesDiffer ()

sameTimePresentFutureCannotRecoverFineFibre :
  INF.FactorsThrough sameTimePresentFuture fineFibreCode → ⊥
sameTimePresentFutureCannotRecoverFineFibre =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      earlyAuthorityAtT1 lateAuthorityAtT1 refl fineFibreCodesDiffer)

sameTime :
  time (fibreAt Temporal.movementEarlyAuthorityHistory Temporal.t1)
  ≡ time (fibreAt Temporal.movementLateAuthorityHistory Temporal.t1)
sameTime = refl

samePresent :
  present (fibreAt Temporal.movementEarlyAuthorityHistory Temporal.t1)
  ≡ present (fibreAt Temporal.movementLateAuthorityHistory Temporal.t1)
samePresent = refl

sameFutureCone :
  futureCone (fibreAt Temporal.movementEarlyAuthorityHistory Temporal.t1)
  ≡ futureCone (fibreAt Temporal.movementLateAuthorityHistory Temporal.t1)
sameFutureCone = refl

authorityAdmissibilityDiffersInsideSameCoarseFibre :
  authorityEnabled (fibreAt Temporal.movementEarlyAuthorityHistory Temporal.t1)
  ≡ authorityEnabled (fibreAt Temporal.movementLateAuthorityHistory Temporal.t1) → ⊥
authorityAdmissibilityDiffersInsideSameCoarseFibre ()

------------------------------------------------------------------------
-- 3. Fibre evolution along a fixed history.
------------------------------------------------------------------------

archiveFibreT1 : HistoryTimeIndexedReceptionFibre
archiveFibreT1 = fibreAt Temporal.archiveTemporalHistory Temporal.t1

archiveFibreT2 : HistoryTimeIndexedReceptionFibre
archiveFibreT2 = fibreAt Temporal.archiveTemporalHistory Temporal.t2

archiveSamePresentAcrossTime : present archiveFibreT1 ≡ present archiveFibreT2
archiveSamePresentAcrossTime = refl

archivePluralAdmissibilityChanges :
  pluralEnabled archiveFibreT1 ≡ pluralEnabled archiveFibreT2 → ⊥
archivePluralAdmissibilityChanges ()

archiveFutureConeChanges :
  futureCone archiveFibreT1 ≡ futureCone archiveFibreT2 → ⊥
archiveFutureConeChanges ()

------------------------------------------------------------------------
-- 4. Bridge into the canonical relational-history fabric interface.
------------------------------------------------------------------------

data FibrePoint : Set where
  earlyPoint latePoint : FibrePoint

data FibreHistoryCode : Set where
  earlyAuthorityHistoryCode lateAuthorityHistoryCode : FibreHistoryCode

data FibreRelationCode : Set where sameReceptionRelation : FibreRelationCode

data FibreGateCode : Set where sameOpenGate : FibreGateCode

data FibreReachableCode : Set where authorityReachable authorityBlocked : FibreReachableCode

data FibreAffordanceCode : Set where authorityAfforded authorityUnafforded : FibreAffordanceCode

data FibreFutureCode : Set where sameMovementFuture : FibreFutureCode

data FibreObservation : Set where sameT1Observation : FibreObservation

fibreFabric : Fabric.RelationalHistoryFabric
fibreFabric =
  record
    { SituatedState = FibrePoint
    ; Observation = FibreObservation
    ; HistoryCode = FibreHistoryCode
    ; RelationCode = FibreRelationCode
    ; GateCode = FibreGateCode
    ; ReachableCode = FibreReachableCode
    ; AffordanceCode = FibreAffordanceCode
    ; FutureConeCode = FibreFutureCode
    ; observe = λ _ → sameT1Observation
    ; historyOf = λ
        { earlyPoint → earlyAuthorityHistoryCode
        ; latePoint → lateAuthorityHistoryCode
        }
    ; relationOf = λ _ → sameReceptionRelation
    ; gateOf = λ _ → sameOpenGate
    ; reachableOf = λ
        { earlyPoint → authorityReachable
        ; latePoint → authorityBlocked
        }
    ; affordanceOf = λ
        { earlyPoint → authorityAfforded
        ; latePoint → authorityUnafforded
        }
    ; futureConeOf = λ _ → sameMovementFuture
    ; fabricReading =
        "Same time/present/future projection can hide distinct history-conditioned reception fibres with different local admissibility."
    }

------------------------------------------------------------------------
-- 5. No-promotion boundaries.
------------------------------------------------------------------------

data ReceptionFibrePromotesVectorBundle : Set where
data ReceptionFibrePromotesGaugeFibre : Set where
data ReceptionFibrePromotesBase369Fibre : Set where
data SameCoarseFibrePromotesSameFineFibre : Set where

receptionFibreDoesNotPromoteVectorBundle : ReceptionFibrePromotesVectorBundle → ⊥
receptionFibreDoesNotPromoteVectorBundle ()

receptionFibreDoesNotPromoteGaugeFibre : ReceptionFibrePromotesGaugeFibre → ⊥
receptionFibreDoesNotPromoteGaugeFibre ()

receptionFibreDoesNotPromoteBase369Fibre : ReceptionFibrePromotesBase369Fibre → ⊥
receptionFibreDoesNotPromoteBase369Fibre ()

sameCoarseFibreDoesNotPromoteSameFineFibre : SameCoarseFibrePromotesSameFineFibre → ⊥
sameCoarseFibreDoesNotPromoteSameFineFibre ()

------------------------------------------------------------------------
-- 6. Canonical boundary.
------------------------------------------------------------------------

record IntellectualReceptionHistoryTimeIndexedFibreBoundary : Set where
  constructor intellectual-reception-history-time-indexed-fibre-boundary
  field
    stratumIsRepresentedAsHistoryTimeIndexedFibre : Bool
    residueIsProjectionOfFibre : Bool
    admissibilityIsProjectionOfFibre : Bool
    futureConeIsProjectionOfFibre : Bool
    sameTimePresentFutureDeterminesFineFibre : Bool
    sameCoarseProjectionDeterminesLocalAdmissibility : Bool
    fibreIsAutomaticallyGeometricBundle : Bool
    fibreIsAutomaticallyBase369Fibre : Bool
    sourceAttributionBoundarySurvivesFibreReasoning : Bool

canonicalIntellectualReceptionHistoryTimeIndexedFibreBoundary :
  IntellectualReceptionHistoryTimeIndexedFibreBoundary
canonicalIntellectualReceptionHistoryTimeIndexedFibreBoundary =
  intellectual-reception-history-time-indexed-fibre-boundary
    true true true true false false false false true
