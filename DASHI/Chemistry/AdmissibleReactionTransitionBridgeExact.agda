module DASHI.Chemistry.AdmissibleReactionTransitionBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL

------------------------------------------------------------------------
-- REPO-NATIVE TYPED BRIDGE OVER THE EXISTING CHEMISTRY KERNEL
--
-- TransitionKernel already records reactants, products, catalysts, rate law,
-- condition/environment, compartments and reachability metadata.  Several of
-- those guards are intentionally solver-neutral String carriers.  This module
-- does not invent their quantitative semantics.  It supplies the missing typed
-- theorem surface: an admitted reaction transition requires an inhabitant of a
-- declared enablement predicate.
------------------------------------------------------------------------

record TypedReactionSemantics
    (transition : Chemistry.Transition) : Set₁ where
  constructor typedReactionSemantics
  field
    State : Set
    Enabled : State → Chemistry.Environment → Set
    step : State → Chemistry.Environment → State
    InvariantRegion : State → Set
    enabledPreservesInvariant :
      (state : State) (environment : Chemistry.Environment) →
      Enabled state environment →
      InvariantRegion state →
      InvariantRegion (step state environment)
    reactantAvailabilityReference : String
    catalystOrCofactorReference : String
    environmentGuardReference : String
    compartmentCompatibilityReference : String
    invariantReference : String

open TypedReactionSemantics public

data AdmittedReaction
    {transition : Chemistry.Transition}
    (semantics : TypedReactionSemantics transition)
    (state : State semantics)
    (environment : Chemistry.Environment) : Set where
  admittedReaction :
    Enabled semantics state environment →
    InvariantRegion semantics state →
    AdmittedReaction semantics state environment

admittedReactionHasEnablement :
  ∀ {transition}
    {semantics : TypedReactionSemantics transition}
    {state environment} →
  AdmittedReaction semantics state environment →
  Enabled semantics state environment
admittedReactionHasEnablement (admittedReaction enabled invariant) = enabled

disabledExcludesAdmittedReaction :
  ∀ {transition}
    {semantics : TypedReactionSemantics transition}
    {state environment} →
  (Enabled semantics state environment → ⊥) →
  AdmittedReaction semantics state environment → ⊥
disabledExcludesAdmittedReaction disabled admitted =
  disabled (admittedReactionHasEnablement admitted)

admittedReactionPreservesInvariant :
  ∀ {transition}
    {semantics : TypedReactionSemantics transition}
    {state environment} →
  AdmittedReaction semantics state environment →
  InvariantRegion semantics (step semantics state environment)
admittedReactionPreservesInvariant
    {semantics = semantics} {state = state} {environment = environment}
    (admittedReaction enabled invariant) =
  enabledPreservesInvariant semantics state environment enabled invariant

------------------------------------------------------------------------
-- Enablement is a hard feasibility gate, distinct from conditional kinetics,
-- probability, odds or hazard once the reaction is enabled.
------------------------------------------------------------------------

record ConditionalReactionWeight
    {transition : Chemistry.Transition}
    (semantics : TypedReactionSemantics transition) : Set₁ where
  constructor conditionalReactionWeight
  field
    Weight : Set
    weight :
      (state : State semantics) →
      (environment : Chemistry.Environment) →
      Enabled semantics state environment →
      Weight
    weightMeaningReference : String

open ConditionalReactionWeight public

------------------------------------------------------------------------
-- Consumer-relative MDL adapter for reaction enablement.
--
-- A compact model is eligible for an enablement-sensitive consumer only if it
-- agrees with the typed physical enablement predicate on the declared scope.
------------------------------------------------------------------------

record ReactionEnablementModel
    {transition : Chemistry.Transition}
    (semantics : TypedReactionSemantics transition) : Set₁ where
  constructor reactionEnablementModel
  field
    Model : Set
    modelEnabled :
      Model → State semantics → Chemistry.Environment → Set
    PhysicallyAdmissible : Model → Set
    descriptionLength : Model → Nat
    Refines : Model → Model → Set
    modelReference : Model → String
    codingConventionReference : String
    scopeReference : String

open ReactionEnablementModel public

EnablementAdequate :
  ∀ {transition}
    {semantics : TypedReactionSemantics transition} →
  (family : ReactionEnablementModel semantics) →
  Model family → Set
EnablementAdequate {semantics = semantics} family model =
  (state : State semantics) →
  (environment : Chemistry.Environment) →
  (modelEnabled family model state environment →
    Enabled semantics state environment)
  ×
  (Enabled semantics state environment →
    modelEnabled family model state environment)

reactionEnablementMDLProblem :
  ∀ {transition}
    {semantics : TypedReactionSemantics transition} →
  ReactionEnablementModel semantics →
  MDL.ConsumerMDLProblem
reactionEnablementMDLProblem family =
  MDL.consumerMDLProblem
    (Model family)
    (PhysicallyAdmissible family)
    (EnablementAdequate family)
    (descriptionLength family)
    (Refines family)
    (modelReference family)
    (codingConventionReference family)
    (scopeReference family)

record ReactionMDLBoundary : Set where
  constructor reactionMDLBoundary
  field
    absentEnablementWitnessMeansTinyProbability : Bool
    absentEnablementWitnessMeansTinyProbabilityIsFalse :
      absentEnablementWitnessMeansTinyProbability ≡ false

    admittedTransitionRequiresEnablement : Bool
    admittedTransitionRequiresEnablementIsTrue :
      admittedTransitionRequiresEnablement ≡ true

    kineticsWeightIsConditionalOnEnablement : Bool
    kineticsWeightIsConditionalOnEnablementIsTrue :
      kineticsWeightIsConditionalOnEnablement ≡ true

    shortestCodeMayEraseConsumerRelevantReactionGuard : Bool
    shortestCodeMayEraseConsumerRelevantReactionGuardIsFalse :
      shortestCodeMayEraseConsumerRelevantReactionGuard ≡ false

    stringGuardCarrierBecomesQuantitativeChemistryHere : Bool
    stringGuardCarrierBecomesQuantitativeChemistryHereIsFalse :
      stringGuardCarrierBecomesQuantitativeChemistryHere ≡ false

canonicalReactionMDLBoundary : ReactionMDLBoundary
canonicalReactionMDLBoundary =
  reactionMDLBoundary false refl true refl true refl false refl false refl
