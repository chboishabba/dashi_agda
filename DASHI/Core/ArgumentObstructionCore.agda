module DASHI.Core.ArgumentObstructionCore where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)

------------------------------------------------------------------------
-- An argument is governed transport from premises to a target conclusion.
-- A fallacy is an obstruction to that transport, not a proof that the
-- target conclusion is false.
------------------------------------------------------------------------

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

data FallacyAxis : Set where
  formalForm
  propositional
  quantification
  syllogistic
  premiseGrounding
  generalisation
  causal
  statistical
  relevance
  relevanceDiversion
  semantic
  scopeProjection
  modal
  temporal
  authority
  emotional
  evidential
  contradiction
  pragmatic
  normative
  probabilistic
  historical
  agency
  comparison
  classification
  resourceAccounting
  optimisation
  : FallacyAxis

record ArgumentCore : Set₁ where
  constructor argumentCore
  field
    Proposition : Set
    Premise     : Set
    Rule        : Set
    Receipt     : Set
    Context     : Set
    Time        : Set
    Meaning     : Set
    Cause       : Set
    Modality    : Set

    premiseProposition   : Premise → Proposition
    conclusion           : Proposition
    applies              : Rule → Premise → Proposition → Set
    supportedBy          : Receipt → Premise → Set
    relevantIn           : Context → Premise → Proposition → Set
    temporallyAdmissible : Time → Premise → Proposition → Set
    semanticallyStable   : Meaning → Premise → Proposition → Set
    causallyAdmissible   : Cause → Premise → Proposition → Set
    modallyAdmissible    : Modality → Premise → Proposition → Set

open ArgumentCore public

record ArgumentWitness (core : ArgumentCore) : Set where
  constructor argumentWitness
  field
    premises : List (Premise core)
    rule     : Rule core
    receipts : List (Receipt core)
    context  : Context core
    time     : Time core
    meaning  : Meaning core
    cause    : Cause core
    modality : Modality core

open ArgumentWitness public

record Obstruction (core : ArgumentCore) : Set₁ where
  constructor obstruction
  field
    axis       : FallacyAxis
    offendingPremise : Premise core
    target     : Proposition core
    Failure    : Set
    witness    : Failure
    conclusionMayStillBeTrue : Bool

open Obstruction public

record AuditResult (core : ArgumentCore) : Set₁ where
  constructor auditResult
  field
    argument     : ArgumentWitness core
    obstructions : List (Obstruction core)
    promotable   : Bool

open AuditResult public

noDetectedObstruction :
  {core : ArgumentCore} →
  (a : ArgumentWitness core) →
  AuditResult core
noDetectedObstruction a = auditResult a [] true

blockedBy :
  {core : ArgumentCore} →
  (a : ArgumentWitness core) →
  Obstruction core →
  AuditResult core
blockedBy a o = auditResult a (o ∷ []) false

fallacyDoesNotRefuteConclusion :
  {core : ArgumentCore} →
  (o : Obstruction core) →
  Bool
fallacyDoesNotRefuteConclusion = conclusionMayStillBeTrue
