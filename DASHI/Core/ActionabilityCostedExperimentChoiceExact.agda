module DASHI.Core.ActionabilityCostedExperimentChoiceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ACTIONABILITY-RELATIVE EXPERIMENT/FIDELITY CHOICE
--
-- Repository-native proof-search objective:
--   choose the least-cost declared information/fidelity action whose supplied
--   witness removes the current obstruction to a robust authorised decision.
--
-- Cost is a declared search/resource order only.  This module does not infer a
-- welfare function, experimental ethics, deployment authority, or probability.
------------------------------------------------------------------------

data InformationMoveKind : Set where
  takeMeasurement
  increaseFidelity
  perturbAndMeasure
  replicateMeasurement
  : InformationMoveKind

record InformationMove : Set where
  constructor informationMove
  field
    kind : InformationMoveKind
    cost : Nat
    moveReference : String
    resourceReference : String
    admissibilityReference : String

open InformationMove public

------------------------------------------------------------------------
-- An obstruction is deliberately application-defined.  In LES this may be an
-- unresolved intervention conflict; in fundamental physics it may be theory
-- equivalence under the current experiment language; elsewhere it may be a
-- fidelity/authority/identifiability obstruction.
------------------------------------------------------------------------

record ActionabilityProblem : Set₁ where
  constructor actionabilityProblem
  field
    Obstruction : Set
    currentObstruction : Obstruction
    Resolves : InformationMove → Obstruction → Set
    obstructionReference : String
    decisionConsumerReference : String
    authorityReference : String

open ActionabilityProblem public

record ResolvingMove (problem : ActionabilityProblem) : Set where
  constructor resolvingMove
  field
    move : InformationMove
    resolves : Resolves problem move (currentObstruction problem)

open ResolvingMove public

------------------------------------------------------------------------
-- Minimality is only among declared alternatives.  A cheaper undeclared or
-- inadmissible move is irrelevant to this receipt; applications must expose the
-- comparison set they wish to optimize over.
------------------------------------------------------------------------

record CheapestResolvingMove
    (problem : ActionabilityProblem)
    (Declared : InformationMove → Set) : Set₁ where
  constructor cheapestResolvingMove
  field
    selected : ResolvingMove problem
    selectedDeclared : Declared (move selected)
    minimal :
      (alternative : InformationMove) →
      Declared alternative →
      Resolves problem alternative (currentObstruction problem) →
      cost (move selected) ≤ cost alternative
    comparisonReference : String

open CheapestResolvingMove public

------------------------------------------------------------------------
-- A stronger receipt makes the post-information decision explicit.  It is not
-- enough that a move changes evidence; it must remove the obstruction and leave
-- a decision with an independent authority witness.
------------------------------------------------------------------------

record ResolvesToAuthorisedDecision
    (problem : ActionabilityProblem)
    (move : InformationMove) : Set₁ where
  constructor resolvesToAuthorisedDecision
  field
    resolvesObstruction : Resolves problem move (currentObstruction problem)
    Decision : Set
    decision : Decision
    robustDecisionReference : String
    authorisedDecisionReference : String

open ResolvesToAuthorisedDecision public

record CheapestAuthorisingInformationMove
    (problem : ActionabilityProblem)
    (Declared : InformationMove → Set) : Set₁ where
  constructor cheapestAuthorisingInformationMove
  field
    selectedMove : InformationMove
    selectedDeclared : Declared selectedMove
    selectedResolution : ResolvesToAuthorisedDecision problem selectedMove
    minimalAmongAuthorising :
      (alternative : InformationMove) →
      Declared alternative →
      ResolvesToAuthorisedDecision problem alternative →
      cost selectedMove ≤ cost alternative
    experimentDesignReference : String

open CheapestAuthorisingInformationMove public

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

record ActionabilityChoiceBoundary : Set where
  constructor actionabilityChoiceBoundary
  field
    cheapestMoveIsAutomaticallyScientificallyBest : Bool
    cheapestMoveIsAutomaticallyScientificallyBestIsFalse :
      cheapestMoveIsAutomaticallyScientificallyBest ≡ false

    measurementThatChangesEvidenceAlwaysRemovesDecisionObstruction : Bool
    measurementThatChangesEvidenceAlwaysRemovesDecisionObstructionIsFalse :
      measurementThatChangesEvidenceAlwaysRemovesDecisionObstruction ≡ false

    fidelityEscalationAndMeasurementCanShareOneSearchObjective : Bool
    fidelityEscalationAndMeasurementCanShareOneSearchObjectiveIsTrue :
      fidelityEscalationAndMeasurementCanShareOneSearchObjective ≡ true

    removingModelConflictAutomaticallyCreatesAuthority : Bool
    removingModelConflictAutomaticallyCreatesAuthorityIsFalse :
      removingModelConflictAutomaticallyCreatesAuthority ≡ false

canonicalActionabilityChoiceBoundary : ActionabilityChoiceBoundary
canonicalActionabilityChoiceBoundary =
  actionabilityChoiceBoundary false refl false refl true refl false refl
