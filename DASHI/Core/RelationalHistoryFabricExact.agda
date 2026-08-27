module DASHI.Core.RelationalHistoryFabricExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor

------------------------------------------------------------------------
-- RELATIONAL HISTORY FABRIC
--
-- This owner composes two orthogonal sources of downstream dependence:
--
--   history / retained path structure
--   relational organisation / interaction structure
--
-- into a staged surface:
--
--   situated state
--     -> coarse present observation
--     -> history-conditioned gate
--     -> effective reachable code
--     -> realized affordance code
--     -> future-cone code.
--
-- The theorem layer is deliberately generic.  It does not claim that every
-- domain uses literal neural gates, ecological interactions, or physical
-- fibres.  Those are application-specific producers.
------------------------------------------------------------------------

record RelationalHistoryFabric : Set₁ where
  field
    SituatedState : Set
    Observation : Set
    HistoryCode : Set
    RelationCode : Set
    GateCode : Set
    ReachableCode : Set
    AffordanceCode : Set
    FutureConeCode : Set

    observe : SituatedState → Observation
    historyOf : SituatedState → HistoryCode
    relationOf : SituatedState → RelationCode
    gateOf : SituatedState → GateCode
    reachableOf : SituatedState → ReachableCode
    affordanceOf : SituatedState → AffordanceCode
    futureConeOf : SituatedState → FutureConeCode

    fabricReading : String

open RelationalHistoryFabric public

------------------------------------------------------------------------
-- Consumer-relative failure of descent.
------------------------------------------------------------------------

record SameObservationDifferentFuture
    (fabric : RelationalHistoryFabric) : Set where
  field
    leftState rightState : SituatedState fabric

    sameObservation :
      observe fabric leftState ≡ observe fabric rightState

    differentFutureCone :
      futureConeOf fabric leftState ≡ futureConeOf fabric rightState → ⊥

open SameObservationDifferentFuture public

futureConeNonFactorability :
  ∀ {fabric : RelationalHistoryFabric} →
  SameObservationDifferentFuture fabric →
  NonFactor.NonFactorabilityWitness
    (observe fabric)
    (futureConeOf fabric)
futureConeNonFactorability witness =
  NonFactor.nonFactorabilityWitness
    (leftState witness)
    (rightState witness)
    (sameObservation witness)
    (differentFutureCone witness)

coarsePresentCannotDetermineFutureCone :
  ∀ {fabric : RelationalHistoryFabric} →
  SameObservationDifferentFuture fabric →
  NonFactor.FactorsThrough
    (observe fabric)
    (futureConeOf fabric) →
  ⊥
coarsePresentCannotDetermineFutureCone witness =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (futureConeNonFactorability witness)

------------------------------------------------------------------------
-- Axis-essentiality witnesses.
--
-- These make the useful distinction explicit:
--   history may matter with relation held fixed;
--   relation may matter with history held fixed.
-- Neither theorem says every application requires both axes.
------------------------------------------------------------------------

record HistoryEssentialForFuture
    (fabric : RelationalHistoryFabric) : Set where
  field
    historyLeft historyRight : SituatedState fabric

    historySameObservation :
      observe fabric historyLeft ≡ observe fabric historyRight

    historyRelationHeldFixed :
      relationOf fabric historyLeft ≡ relationOf fabric historyRight

    historyActuallyDiffers :
      historyOf fabric historyLeft ≡ historyOf fabric historyRight → ⊥

    historyFutureDiffers :
      futureConeOf fabric historyLeft ≡ futureConeOf fabric historyRight → ⊥

open HistoryEssentialForFuture public

record RelationEssentialForFuture
    (fabric : RelationalHistoryFabric) : Set where
  field
    relationLeft relationRight : SituatedState fabric

    relationSameObservation :
      observe fabric relationLeft ≡ observe fabric relationRight

    relationHistoryHeldFixed :
      historyOf fabric relationLeft ≡ historyOf fabric relationRight

    relationActuallyDiffers :
      relationOf fabric relationLeft ≡ relationOf fabric relationRight → ⊥

    relationFutureDiffers :
      futureConeOf fabric relationLeft ≡ futureConeOf fabric relationRight → ⊥

open RelationEssentialForFuture public

historyEssentialBlocksPresentOnlyFutureModel :
  ∀ {fabric : RelationalHistoryFabric} →
  HistoryEssentialForFuture fabric →
  NonFactor.FactorsThrough
    (observe fabric)
    (futureConeOf fabric) →
  ⊥
historyEssentialBlocksPresentOnlyFutureModel witness =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      (historyLeft witness)
      (historyRight witness)
      (historySameObservation witness)
      (historyFutureDiffers witness))

relationEssentialBlocksPresentOnlyFutureModel :
  ∀ {fabric : RelationalHistoryFabric} →
  RelationEssentialForFuture fabric →
  NonFactor.FactorsThrough
    (observe fabric)
    (futureConeOf fabric) →
  ⊥
relationEssentialBlocksPresentOnlyFutureModel witness =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      (relationLeft witness)
      (relationRight witness)
      (relationSameObservation witness)
      (relationFutureDiffers witness))

------------------------------------------------------------------------
-- Propagation witness.
--
-- This does not assert a universal causal law.  It packages the stronger
-- application-specific case where changed history is witnessed all the way
-- through gate, reachable structure, affordance, and continuation.
------------------------------------------------------------------------

record HistoryPropagationWitness
    (fabric : RelationalHistoryFabric) : Set where
  field
    propagationLeft propagationRight : SituatedState fabric

    propagationSameObservation :
      observe fabric propagationLeft ≡ observe fabric propagationRight

    propagationHistoryDiffers :
      historyOf fabric propagationLeft ≡ historyOf fabric propagationRight → ⊥

    propagationGateDiffers :
      gateOf fabric propagationLeft ≡ gateOf fabric propagationRight → ⊥

    propagationReachableDiffers :
      reachableOf fabric propagationLeft ≡ reachableOf fabric propagationRight → ⊥

    propagationAffordanceDiffers :
      affordanceOf fabric propagationLeft ≡ affordanceOf fabric propagationRight → ⊥

    propagationFutureDiffers :
      futureConeOf fabric propagationLeft ≡ futureConeOf fabric propagationRight → ⊥

open HistoryPropagationWitness public

historyPropagationBlocksCoarseFutureDescent :
  ∀ {fabric : RelationalHistoryFabric} →
  HistoryPropagationWitness fabric →
  NonFactor.FactorsThrough
    (observe fabric)
    (futureConeOf fabric) →
  ⊥
historyPropagationBlocksCoarseFutureDescent witness =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      (propagationLeft witness)
      (propagationRight witness)
      (propagationSameObservation witness)
      (propagationFutureDiffers witness))

------------------------------------------------------------------------
-- Exact finite specimen.
------------------------------------------------------------------------

data ToySituatedState : Set where
  sameNowOpenHistory sameNowClosedHistory : ToySituatedState

data ToyObservation : Set where
  sameNow : ToyObservation

data ToyHistoryCode : Set where
  flexibleHistory committedHistory : ToyHistoryCode

data ToyRelationCode : Set where
  sameRelation : ToyRelationCode

data ToyGateCode : Set where
  openGate closedGate : ToyGateCode

data ToyReachableCode : Set where
  broadReachable contractedReachable : ToyReachableCode

data ToyAffordanceCode : Set where
  broadAffordance contractedAffordance : ToyAffordanceCode

data ToyFutureConeCode : Set where
  broadFutureCone contractedFutureCone : ToyFutureConeCode

toyFabric : RelationalHistoryFabric
toyFabric =
  record
    { SituatedState = ToySituatedState
    ; Observation = ToyObservation
    ; HistoryCode = ToyHistoryCode
    ; RelationCode = ToyRelationCode
    ; GateCode = ToyGateCode
    ; ReachableCode = ToyReachableCode
    ; AffordanceCode = ToyAffordanceCode
    ; FutureConeCode = ToyFutureConeCode
    ; observe = λ _ → sameNow
    ; historyOf = λ
        { sameNowOpenHistory → flexibleHistory
        ; sameNowClosedHistory → committedHistory
        }
    ; relationOf = λ _ → sameRelation
    ; gateOf = λ
        { sameNowOpenHistory → openGate
        ; sameNowClosedHistory → closedGate
        }
    ; reachableOf = λ
        { sameNowOpenHistory → broadReachable
        ; sameNowClosedHistory → contractedReachable
        }
    ; affordanceOf = λ
        { sameNowOpenHistory → broadAffordance
        ; sameNowClosedHistory → contractedAffordance
        }
    ; futureConeOf = λ
        { sameNowOpenHistory → broadFutureCone
        ; sameNowClosedHistory → contractedFutureCone
        }
    ; fabricReading =
        "A shared coarse present may hide histories that propagate through different gate, reachable, affordance, and future-cone codes."
    }

canonicalHistoryPropagationWitness : HistoryPropagationWitness toyFabric
canonicalHistoryPropagationWitness =
  record
    { propagationLeft = sameNowOpenHistory
    ; propagationRight = sameNowClosedHistory
    ; propagationSameObservation = refl
    ; propagationHistoryDiffers = λ ()
    ; propagationGateDiffers = λ ()
    ; propagationReachableDiffers = λ ()
    ; propagationAffordanceDiffers = λ ()
    ; propagationFutureDiffers = λ ()
    }

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record RelationalHistoryFabricBoundary : Set where
  constructor relationalHistoryFabricBoundary
  field
    historyBearingAloneImpliesPathDependence : Bool
    historyBearingAloneImpliesPathDependenceIsFalse :
      historyBearingAloneImpliesPathDependence ≡ false

    relationDifferenceAlwaysChangesFuture : Bool
    relationDifferenceAlwaysChangesFutureIsFalse :
      relationDifferenceAlwaysChangesFuture ≡ false

    gateCodeIsAutomaticallyNeuralMechanism : Bool
    gateCodeIsAutomaticallyNeuralMechanismIsFalse :
      gateCodeIsAutomaticallyNeuralMechanism ≡ false

    reachableCodeIsAutomaticallyPhysicalReachability : Bool
    reachableCodeIsAutomaticallyPhysicalReachabilityIsFalse :
      reachableCodeIsAutomaticallyPhysicalReachability ≡ false

    applicationWitnessCanEstablishHistoryToFuturePropagation : Bool
    applicationWitnessCanEstablishHistoryToFuturePropagationIsTrue :
      applicationWitnessCanEstablishHistoryToFuturePropagation ≡ true

canonicalRelationalHistoryFabricBoundary : RelationalHistoryFabricBoundary
canonicalRelationalHistoryFabricBoundary =
  relationalHistoryFabricBoundary
    false refl
    false refl
    false refl
    false refl
    true refl
