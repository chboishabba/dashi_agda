module DASHI.Philosophy.TopologyChangeCriteria where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Changed state, feedback, transition system, and topology are separate.

data ChangeKind : Set where
  stateChange : ChangeKind
  feedbackChange : ChangeKind
  transitionSystemChange : ChangeKind
  topologyChange : ChangeKind

record TopologicalSystem
       (State Path Neighbourhood Connectivity Code : Set) : Set₁ where
  field
    state : State
    admissiblePath : Path → Set
    neighbourhood : Neighbourhood → Set
    connected : Connectivity → Set
    topologyCode : Code

open TopologicalSystem public

record TransitionChangeWitness
       {State Path Neighbourhood Connectivity Code : Set}
       (old new : TopologicalSystem State Path Neighbourhood Connectivity Code) : Set₁ where
  field
    changedAdmissiblePath :
      Path

    oldPathStatus :
      admissiblePath old changedAdmissiblePath

    newPathDifference :
      Set

open TransitionChangeWitness public

record TopologyChangeWitness
       {State Path Neighbourhood Connectivity Code : Set}
       (old new : TopologicalSystem State Path Neighbourhood Connectivity Code) : Set₁ where
  field
    codeChanged :
      Set

    neighbourhoodChanged :
      Neighbourhood

    neighbourhoodDifference :
      Set

    connectivityChanged :
      Connectivity

    connectivityDifference :
      Set

    admissiblePathsChanged :
      TransitionChangeWitness old new

open TopologyChangeWitness public

record ChangePromotionBoundary : Set where
  constructor changePromotionBoundary
  field
    changedStateImpliesChangedFeedback : Bool
    changedFeedbackImpliesChangedTransitionSystem : Bool
    changedTransitionSystemImpliesChangedTopology : Bool
    topologyRequiresNeighbourhoodOrConnectivityWitness : Bool

open ChangePromotionBoundary public

canonicalChangePromotionBoundary : ChangePromotionBoundary
canonicalChangePromotionBoundary =
  changePromotionBoundary
    false
    false
    false
    true

canonicalFeedbackDoesNotAutomaticallyChangeTopology :
  changedTransitionSystemImpliesChangedTopology canonicalChangePromotionBoundary
  ≡ false
canonicalFeedbackDoesNotAutomaticallyChangeTopology = refl
