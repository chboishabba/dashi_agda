module DASHI.Governance.SexedHistoricalEffectiveFibreTransportExact where

------------------------------------------------------------------------
-- FORMAL TRANSITION != LOCALLY ADMISSIBLE FIBRE TRANSPORT
--
-- This owner lifts the finite M/F comparison-channel algebra into a
-- history-conditioned transport surface.  A formal arrow can exist in the
-- abstract comparison category while the corresponding situated transition is
-- unavailable, unresolved, or admitted only in a particular historical/power/
-- evidence fibre.
--
-- The finite carrier is a DASHI comparison fixture.  It does not claim that
-- gender is exhaustively binary or that the declared contexts are empirical
-- laws about historical populations.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.RelationalHistoryFabricExact as History
import DASHI.Core.EpistemicSuspensionExact as Suspension
import DASHI.Governance.SexedHistoricalBase369TransitionPathExact as Path
import DASHI.Governance.SexedHistoricalChoiceConeBridgeExact as Choice

------------------------------------------------------------------------
-- 1. Formal channels exist independently of situated reachability.
------------------------------------------------------------------------

data FormalChannel : Set where
  formalMM formalMF formalFM formalFF : FormalChannel

data HistoricalFibre : Set where
  inheritedClosedFibre
  contestedDependentFibre
  pluralResourceFibre
  reciprocalOpenFibre
  : HistoricalFibre

data LocalReachability : Set where
  locallyBlocked locallyUnresolved locallyReachable : LocalReachability

formalExists : FormalChannel → Bool
formalExists _ = true

localReachability : HistoricalFibre → FormalChannel → LocalReachability
localReachability inheritedClosedFibre formalMM = locallyReachable
localReachability inheritedClosedFibre formalMF = locallyReachable
localReachability inheritedClosedFibre formalFM = locallyBlocked
localReachability inheritedClosedFibre formalFF = locallyUnresolved

localReachability contestedDependentFibre formalMM = locallyReachable
localReachability contestedDependentFibre formalMF = locallyReachable
localReachability contestedDependentFibre formalFM = locallyUnresolved
localReachability contestedDependentFibre formalFF = locallyUnresolved

localReachability pluralResourceFibre formalMM = locallyReachable
localReachability pluralResourceFibre formalMF = locallyReachable
localReachability pluralResourceFibre formalFM = locallyReachable
localReachability pluralResourceFibre formalFF = locallyReachable

localReachability reciprocalOpenFibre _ = locallyReachable

formalMFExistsEverywhere : formalExists formalMF ≡ true
formalMFExistsEverywhere = refl

formalFMExistsEvenWhereLocallyBlocked : formalExists formalFM ≡ true
formalFMExistsEvenWhereLocallyBlocked = refl

inheritedClosedBlocksFormalFM :
  localReachability inheritedClosedFibre formalFM ≡ locallyBlocked
inheritedClosedBlocksFormalFM = refl

pluralResourceAdmitsFormalFM :
  localReachability pluralResourceFibre formalFM ≡ locallyReachable
pluralResourceAdmitsFormalFM = refl

------------------------------------------------------------------------
-- 2. Same formal channel, different local transport status.
------------------------------------------------------------------------

record SituatedFormalTransition : Set where
  constructor situated-transition
  field
    fibre : HistoricalFibre
    channel : FormalChannel
open SituatedFormalTransition public

data FormalSurface : Set where
  sameFormalFM : FormalSurface

formalSurface : SituatedFormalTransition → FormalSurface
formalSurface _ = sameFormalFM

reachabilitySurface : SituatedFormalTransition → LocalReachability
reachabilitySurface t = localReachability (fibre t) (channel t)

closedFM openFM : SituatedFormalTransition
closedFM = situated-transition inheritedClosedFibre formalFM
openFM = situated-transition pluralResourceFibre formalFM

formalTransitionCannotRecoverLocalReachability :
  INF.FactorsThrough formalSurface reachabilitySurface → ⊥
formalTransitionCannotRecoverLocalReachability =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness closedFM openFM refl (λ ()))

------------------------------------------------------------------------
-- 3. Ternary local admission.  Blocked / unresolved / reachable remain
--    distinct and map to reject / suspend-refine / accept.
------------------------------------------------------------------------

reachabilityDisposition : LocalReachability → Suspension.EpistemicDisposition
reachabilityDisposition locallyBlocked = Suspension.rejectHere
reachabilityDisposition locallyUnresolved = Suspension.suspendAndRefine
reachabilityDisposition locallyReachable = Suspension.acceptHere

unresolvedTransportRequestsRefinement :
  reachabilityDisposition locallyUnresolved ≡ Suspension.suspendAndRefine
unresolvedTransportRequestsRefinement = refl

------------------------------------------------------------------------
-- 4. History-bearing staged fabric.  Present/formal equality does not erase
--    the history-conditioned gate, reachability, affordance or future cone.
------------------------------------------------------------------------

data TransportState : Set where
  samePresentClosed samePresentOpen : TransportState

data PresentObservation : Set where sameFormalPresent : PresentObservation

data HistoryCode : Set where inheritedClosure pluralisedHistory : HistoryCode

data RelationCode : Set where sameReciprocalQuestion : RelationCode

data GateCode : Set where closedTransportGate openTransportGate : GateCode

data ReachableCode : Set where contractedTransitions broadTransitions : ReachableCode

data AffordanceCode : Set where inheritedAffordance relationalAffordance : AffordanceCode

data FutureConeCode : Set where inheritedCone expandedRelationalCone : FutureConeCode

transportHistoryFabric : History.RelationalHistoryFabric
transportHistoryFabric =
  record
    { History.SituatedState = TransportState
    ; History.Observation = PresentObservation
    ; History.HistoryCode = HistoryCode
    ; History.RelationCode = RelationCode
    ; History.GateCode = GateCode
    ; History.ReachableCode = ReachableCode
    ; History.AffordanceCode = AffordanceCode
    ; History.FutureConeCode = FutureConeCode
    ; History.observe = λ _ → sameFormalPresent
    ; History.historyOf = λ
        { samePresentClosed → inheritedClosure
        ; samePresentOpen → pluralisedHistory
        }
    ; History.relationOf = λ _ → sameReciprocalQuestion
    ; History.gateOf = λ
        { samePresentClosed → closedTransportGate
        ; samePresentOpen → openTransportGate
        }
    ; History.reachableOf = λ
        { samePresentClosed → contractedTransitions
        ; samePresentOpen → broadTransitions
        }
    ; History.affordanceOf = λ
        { samePresentClosed → inheritedAffordance
        ; samePresentOpen → relationalAffordance
        }
    ; History.futureConeOf = λ
        { samePresentClosed → inheritedCone
        ; samePresentOpen → expandedRelationalCone
        }
    ; History.fabricReading =
        "The same formal transition surface can sit over histories with different local transport gates, reachable transitions, relational affordances, and future cones."
    }

canonicalTransportHistoryPropagation :
  History.HistoryPropagationWitness transportHistoryFabric
canonicalTransportHistoryPropagation =
  record
    { History.propagationLeft = samePresentClosed
    ; History.propagationRight = samePresentOpen
    ; History.propagationSameObservation = refl
    ; History.propagationHistoryDiffers = λ ()
    ; History.propagationGateDiffers = λ ()
    ; History.propagationReachableDiffers = λ ()
    ; History.propagationAffordanceDiffers = λ ()
    ; History.propagationFutureDiffers = λ ()
    }

sameFormalPresentCannotRecoverFutureCone :
  INF.FactorsThrough
    (History.observe transportHistoryFabric)
    (History.futureConeOf transportHistoryFabric) → ⊥
sameFormalPresentCannotRecoverFutureCone =
  History.historyPropagationBlocksCoarseFutureDescent
    canonicalTransportHistoryPropagation

------------------------------------------------------------------------
-- 5. Cross-pollination boundaries.
------------------------------------------------------------------------

data FormalCategoryArrowImpliesEffectiveReachability : Set where

data LocalReachabilityImpliesConceivedAvailability : Set where

data LocallyBlockedMeansOntologicallyImpossible : Set where

data CurrentGateErasesTransportHistory : Set where

formalArrowDoesNotImplyEffectiveReachability :
  FormalCategoryArrowImpliesEffectiveReachability → ⊥
formalArrowDoesNotImplyEffectiveReachability ()

localReachabilityDoesNotImplyConceivedAvailability :
  LocalReachabilityImpliesConceivedAvailability → ⊥
localReachabilityDoesNotImplyConceivedAvailability ()

localBlockDoesNotMakeFormalTransitionOntologicallyImpossible :
  LocallyBlockedMeansOntologicallyImpossible → ⊥
localBlockDoesNotMakeFormalTransitionOntologicallyImpossible ()

currentGateDoesNotEraseTransportHistory : CurrentGateErasesTransportHistory → ⊥
currentGateDoesNotEraseTransportHistory ()

formalEffectiveConceivedBoundaryStillAuthoritative :
  INF.FactorsThrough Choice.formalRight Choice.effectiveChoice → ⊥
formalEffectiveConceivedBoundaryStillAuthoritative =
  Choice.formalRightCannotRecoverEffectiveChoice

pathCategoryStillExistsAbstractly : Bool
pathCategoryStillExistsAbstractly =
  Path.SexedHistoricalBase369TransitionPathBoundary.finiteTwoObjectPathCategoryConstructed
    Path.canonicalSexedHistoricalBase369TransitionPathBoundary

record EffectiveFibreTransportBoundary : Set where
  constructor effective-fibre-transport-boundary
  field
    formalArrowEqualsLocalReachability : Bool
    localReachabilityEqualsConceivedChoice : Bool
    blockedEdgeMeansFormalArrowAbsent : Bool
    unresolvedEdgeRequestsRefinement : Bool
    retainedHistoryCanChangeFutureConeAtSamePresent : Bool

canonicalEffectiveFibreTransportBoundary : EffectiveFibreTransportBoundary
canonicalEffectiveFibreTransportBoundary =
  effective-fibre-transport-boundary false false false true true
