module DASHI.Physics.Foundations.ContextConditionedTrajectoryWeightExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Boundary/source/context data may change the weights of already-admissible
-- trajectories without changing the underlying admissibility relation.
--
-- This is the generic owner needed by aperture/slit, finite-source wake,
-- masked optical transport, and related mode-selection consumers.
------------------------------------------------------------------------

record ContextConditionedTrajectoryWeight : Set₁ where
  field
    Context : Set
    Trajectory : Set
    Weight : Set

    admissible : Trajectory → Set
    weightAt : Context → Trajectory → Weight

    weightingReading : String

open ContextConditionedTrajectoryWeight public

record SameTrajectoryContextWeightChange
    (surface : ContextConditionedTrajectoryWeight) : Set where
  field
    trajectory : Trajectory surface
    contextLeft : Context surface
    contextRight : Context surface

    WeightDifference : Set
    weightDifferenceWitness :
      WeightDifference

    differenceReadsWeights :
      Weight surface × Weight surface

    differenceReadsWeightsIsExact :
      differenceReadsWeights
      ≡
      ( weightAt surface contextLeft trajectory
      , weightAt surface contextRight trajectory
      )

open SameTrajectoryContextWeightChange public

data ToySourceContext : Set where
  narrowSource : ToySourceContext
  broadSource : ToySourceContext

data ToyMode : Set where
  centralMode : ToyMode
  obliqueMode : ToyMode

data ToyWeight : Set where
  weakWeight : ToyWeight
  strongWeight : ToyWeight

data ToyWeightDifference : Set where
  contextChangesObliqueWeight : ToyWeightDifference

data ToyAdmissible : ToyMode → Set where
  centralAdmissible : ToyAdmissible centralMode
  obliqueAdmissible : ToyAdmissible obliqueMode

canonicalContextConditionedTrajectoryWeight :
  ContextConditionedTrajectoryWeight
canonicalContextConditionedTrajectoryWeight =
  record
    { Context = ToySourceContext
    ; Trajectory = ToyMode
    ; Weight = ToyWeight
    ; admissible = ToyAdmissible
    ; weightAt = λ
        { narrowSource centralMode → strongWeight
        ; narrowSource obliqueMode → weakWeight
        ; broadSource centralMode → strongWeight
        ; broadSource obliqueMode → strongWeight
        }
    ; weightingReading =
        "Source/boundary context controls weights on an admissible trajectory family; admissibility and excitation strength are different structures."
    }

canonicalSameTrajectoryContextWeightChange :
  SameTrajectoryContextWeightChange canonicalContextConditionedTrajectoryWeight
canonicalSameTrajectoryContextWeightChange =
  record
    { trajectory = obliqueMode
    ; contextLeft = narrowSource
    ; contextRight = broadSource
    ; WeightDifference = ToyWeightDifference
    ; weightDifferenceWitness = contextChangesObliqueWeight
    ; differenceReadsWeights = weakWeight , strongWeight
    ; differenceReadsWeightsIsExact = refl
    }

record ContextConditionedWeightBoundary : Set where
  constructor contextConditionedWeightBoundary
  field
    admissibleMeansStronglyWeighted : Bool
    admissibleMeansStronglyWeightedIsFalse :
      admissibleMeansStronglyWeighted ≡ false

    sourceWeightingChangesUnderlyingLawAutomatically : Bool
    sourceWeightingChangesUnderlyingLawAutomaticallyIsFalse :
      sourceWeightingChangesUnderlyingLawAutomatically ≡ false

    contextConditioningIsQuantumEntanglementByDefinition : Bool
    contextConditioningIsQuantumEntanglementByDefinitionIsFalse :
      contextConditioningIsQuantumEntanglementByDefinition ≡ false

canonicalContextConditionedWeightBoundary : ContextConditionedWeightBoundary
canonicalContextConditionedWeightBoundary =
  contextConditionedWeightBoundary
    false refl
    false refl
    false refl
