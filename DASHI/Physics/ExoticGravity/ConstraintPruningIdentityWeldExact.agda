module DASHI.Physics.ExoticGravity.ConstraintPruningIdentityWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.AntigravityConstraintPruningVsBundlePaymentExact as Pruning
import DASHI.Physics.ExoticGravity.SuperconductingConstraintObservationRouteExact as Route
import DASHI.Physics.ExoticGravity.SuperconductingConstraintSourceAttributionMigrationExact as SourceMigration

record ConstraintPruningIdentityWeld
    (receipt : Pruning.ConstraintPruningReceipt) : Set where
  constructor constraint-pruning-identity-weld
  field
    routeConstraintMatches :
      Route.constraint (Pruning.typedObservationRoute receipt)
        ≡ Pruning.constraint receipt
    sourceCandidateConstraintMatches :
      SourceMigration.constraint (Pruning.sourceCandidate receipt)
        ≡ Pruning.constraint receipt

open ConstraintPruningIdentityWeld public

hathawayIdentityWeld :
  ConstraintPruningIdentityWeld Pruning.hathawayNullPruning
hathawayIdentityWeld = constraint-pruning-identity-weld refl refl

tajmarTransitionIdentityWeld :
  ConstraintPruningIdentityWeld Pruning.tajmarTransitionPruning
tajmarTransitionIdentityWeld = constraint-pruning-identity-weld refl refl

tajmarMagnitudeIdentityWeld :
  ConstraintPruningIdentityWeld Pruning.tajmarMagnitudePruning
tajmarMagnitudeIdentityWeld = constraint-pruning-identity-weld refl refl

nasaRFIdentityWeld :
  ConstraintPruningIdentityWeld Pruning.nasaRFArtifactGuidance
nasaRFIdentityWeld = constraint-pruning-identity-weld refl refl

record ConstraintPruningIdentityBoundary : Set where
  constructor constraint-pruning-identity-boundary
  field
    routeMayFloatToDifferentConstraint : Bool
    sourceCandidateMayFloatToDifferentConstraint : Bool
    exactIdentityWeldRequiredBeforeConsumerUse : Bool

canonicalConstraintPruningIdentityBoundary : ConstraintPruningIdentityBoundary
canonicalConstraintPruningIdentityBoundary =
  constraint-pruning-identity-boundary false false true
