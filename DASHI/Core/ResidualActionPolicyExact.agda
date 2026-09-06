module DASHI.Core.ResidualActionPolicyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Actionability
import DASHI.Core.MechanismModelDiscriminationExact as Model

------------------------------------------------------------------------
-- TYPED RESIDUAL -> ACTION POLICY
------------------------------------------------------------------------

data ResidualActionKind : Set where
  reopen
  measure
  perturb
  hold
  acceptForConsumer
  refute
  : ResidualActionKind

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
  residualActionBoundary false refl false refl false refl true refl true refl true refl
