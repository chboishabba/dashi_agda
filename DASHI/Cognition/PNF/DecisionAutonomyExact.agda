module DASHI.Cognition.PNF.DecisionAutonomyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Cognition.PNF.UnifiedDecisionDynamicsExact as Decision

------------------------------------------------------------------------
-- Autonomy is deliberately multi-axis.  An observed action is not enough to
-- reconstruct accessibility, refinement, revision opportunity or coercive
-- actuation constraints.
------------------------------------------------------------------------

record AutonomyAxes : Set where
  constructor autonomyAxes
  field
    relevantAlternativesAccessible : Bool
    decisionRelevantRefinement : Bool
    revisionOpportunity : Bool
    actuationNotExternallyForced : Bool
    unresolvedAlternativesPreserved : Bool

open AutonomyAxes public

record Autonomous (a : AutonomyAxes) : Set where
  constructor autonomous
  field
    accessOK : relevantAlternativesAccessible a ≡ true
    refinementOK : decisionRelevantRefinement a ≡ true
    revisionOK : revisionOpportunity a ≡ true
    actuationOK : actuationNotExternallyForced a ≡ true
    residualOK : unresolvedAlternativesPreserved a ≡ true

open Autonomous public

freeAxes : AutonomyAxes
freeAxes = autonomyAxes true true true true true

constrainedAxes : AutonomyAxes
constrainedAxes = autonomyAxes false true false true true

freeIsAutonomous : Autonomous freeAxes
freeIsAutonomous = autonomous refl refl refl refl refl

constrainedNotAutonomous : Autonomous constrainedAxes → ⊥
constrainedNotAutonomous a with accessOK a
... | ()

------------------------------------------------------------------------
-- Same emitted action, different autonomy state.
------------------------------------------------------------------------

record ActionEpisode : Set where
  constructor actionEpisode
  field
    axes : AutonomyAxes
    emitted : Decision.ExecutedAction

open ActionEpisode public

autonomousWithdrawal : ActionEpisode
autonomousWithdrawal = actionEpisode freeAxes Decision.supportAction

constrainedWithdrawal : ActionEpisode
constrainedWithdrawal = actionEpisode constrainedAxes Decision.supportAction

sameActionDoesNotDetermineAutonomy :
  emitted autonomousWithdrawal ≡ emitted constrainedWithdrawal
  × (Autonomous (axes autonomousWithdrawal))
  × (Autonomous (axes constrainedWithdrawal) → ⊥)
sameActionDoesNotDetermineAutonomy =
  refl , (freeIsAutonomous , constrainedNotAutonomous)

record AutonomyBoundary : Set where
  constructor autonomyBoundary
  field
    actionEqualsAutonomy : Bool
    accessibilityAloneEqualsAutonomy : Bool
    formalValidityAloneEqualsAutonomy : Bool
    autonomyIsMultidimensional : Bool

canonicalAutonomyBoundary : AutonomyBoundary
canonicalAutonomyBoundary = autonomyBoundary false false false true
