module DASHI.Core.ResidualActionPolicyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Actionability
import DASHI.Core.MechanismModelDiscriminationExact as Model

------------------------------------------------------------------------
-- TYPED RESIDUAL -> ACTION POLICY
--
-- A residual is not itself an actuator command.  This owner separates the
-- evidentiary residual from the next admissible action and requires a
-- proof-bearing admission appropriate to that action kind.
------------------------------------------------------------------------

data ResidualActionKind : Set where
  reopen : ResidualActionKind
  measure : ResidualActionKind
  perturb : ResidualActionKind
  hold : ResidualActionKind
  acceptForConsumer : ResidualActionKind
  refute : ResidualActionKind


record ResidualActionSemantics : Set₁ where
  constructor residualActionSemantics
  field
    ReopenAdmission : Model.ModelResidual → Model.DependencyScopedReopen → Set
    MeasureAdmission : Model.ModelResidual → Actionability.InformationMove → Set
    PerturbAdmission : Model.ModelResidual → Actionability.InformationMove → Set
    HoldAdmission : Model.ModelResidual → Set
    ConsumerClosureAdmission : Model.ModelResidual → Set
    RefutationAdmission : Model.ModelResidual → Set

open ResidualActionSemantics public

data AdmissibleResidualAction
    (semantics : ResidualActionSemantics)
    (residual : Model.ModelResidual) :
    ResidualActionKind → Set₁ where

  reopenAction :
    (reopening : Model.DependencyScopedReopen) →
    ReopenAdmission semantics residual reopening →
    AdmissibleResidualAction semantics residual reopen

  measureAction :
    (move : Actionability.InformationMove) →
    MeasureAdmission semantics residual move →
    AdmissibleResidualAction semantics residual measure

  perturbAction :
    (move : Actionability.InformationMove) →
    PerturbAdmission semantics residual move →
    AdmissibleResidualAction semantics residual perturb

  holdAction :
    HoldAdmission semantics residual →
    AdmissibleResidualAction semantics residual hold

  acceptAction :
    ConsumerClosureAdmission semantics residual →
    AdmissibleResidualAction semantics residual acceptForConsumer

  refuteAction :
    Model.residualClass residual ≡ Model.falsified →
    RefutationAdmission semantics residual →
    AdmissibleResidualAction semantics residual refute

------------------------------------------------------------------------
-- Information-move bridge.
--
-- Measurement and perturbation reuse the existing actionability carrier.  The
-- adapter is deliberately one-way: a generic information move is not by itself
-- a residual-policy admission.
------------------------------------------------------------------------

measurementMove :
  Nat → String → String → String → Actionability.InformationMove
measurementMove cost reference resource admissibility =
  Actionability.informationMove
    Actionability.takeMeasurement cost reference resource admissibility

perturbAndMeasureMove :
  Nat → String → String → String → Actionability.InformationMove
perturbAndMeasureMove cost reference resource admissibility =
  Actionability.informationMove
    Actionability.perturbAndMeasure cost reference resource admissibility

------------------------------------------------------------------------
-- Least-privilege policy receipt.
------------------------------------------------------------------------

record ResidualActionPolicy : Set₁ where
  constructor residualActionPolicy
  field
    semantics : ResidualActionSemantics
    chooseKind : Model.ModelResidual → ResidualActionKind
    actionReference : Model.ModelResidual → String
    authorityReference : Model.ModelResidual → String
    leastPrivilegeReference : String

open ResidualActionPolicy public

record ResidualActionBoundary : Set where
  constructor residualActionBoundary
  field
    residualAutomaticallyAuthorisesAction : Bool
    residualAutomaticallyAuthorisesActionIsFalse :
      residualAutomaticallyAuthorisesAction ≡ false

    discriminatingResidualAutomaticallyReopensEveryCarrier : Bool
    discriminatingResidualAutomaticallyReopensEveryCarrierIsFalse :
      discriminatingResidualAutomaticallyReopensEveryCarrier ≡ false

    measurementAndPerturbationRequireSameAuthority : Bool
    measurementAndPerturbationRequireSameAuthorityIsFalse :
      measurementAndPerturbationRequireSameAuthority ≡ false

    consumerClosureMayPermitStoppingBeforeModelIdentity : Bool
    consumerClosureMayPermitStoppingBeforeModelIdentityIsTrue :
      consumerClosureMayPermitStoppingBeforeModelIdentity ≡ true

    refutationRequiresMoreThanTension : Bool
    refutationRequiresMoreThanTensionIsTrue :
      refutationRequiresMoreThanTension ≡ true

    holdIsAFirstClassNonRefutationAction : Bool
    holdIsAFirstClassNonRefutationActionIsTrue :
      holdIsAFirstClassNonRefutationAction ≡ true

canonicalResidualActionBoundary : ResidualActionBoundary
canonicalResidualActionBoundary =
  residualActionBoundary
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
