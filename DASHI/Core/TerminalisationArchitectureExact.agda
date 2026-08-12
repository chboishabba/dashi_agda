module DASHI.Core.TerminalisationArchitectureExact where

------------------------------------------------------------------------
-- TERMINALISATION / MEMORY / COMMAND ARCHITECTURE
--
-- This module formalises the distinction between retained historical content
-- and later action/classification state.  It deliberately does not identify
-- any particular political, clinical, legal, or psychological application
-- with the generic construction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Event -> harm -> interpretation -> response -> classification -> action
-- remains a typed causal chain: later coordinates do not overwrite earlier
-- ones.
------------------------------------------------------------------------

record CausalClassificationState
    (Event Harm Interpretation Response Classification Action : Set) : Set₁ where
  constructor causalClassificationState
  field
    event : Event
    harm : Harm
    interpretation : Interpretation
    response : Response
    classification : Classification
    action : Action

open CausalClassificationState public

------------------------------------------------------------------------
-- Memory and command are separate coordinates.
------------------------------------------------------------------------

record ProvenanceMemory
    (Event Valuation Salience Confidence Phase ActionWeight Provenance : Set) : Set₁ where
  constructor provenanceMemory
  field
    rememberedEvent : Event
    valuation : Valuation
    salience : Salience
    confidence : Confidence
    phase : Phase
    actionWeight : ActionWeight
    provenance : Provenance

open ProvenanceMemory public

record EventProvenancePreservingUpdate
    {Event Valuation Salience Confidence Phase ActionWeight Provenance : Set}
    (update : ProvenanceMemory Event Valuation Salience Confidence Phase ActionWeight Provenance →
              ProvenanceMemory Event Valuation Salience Confidence Phase ActionWeight Provenance) : Set₁ where
  constructor eventProvenancePreservingUpdate
  field
    eventPreserved : ∀ memory → rememberedEvent (update memory) ≡ rememberedEvent memory
    provenancePreserved : ∀ memory → provenance (update memory) ≡ provenance memory

open EventProvenancePreservingUpdate public

------------------------------------------------------------------------
-- Classification is represented as a revisable edge, not an identity rewrite.
------------------------------------------------------------------------

record ClassificationEdge (Subject Class Evidence Revision : Set) : Set₁ where
  constructor classificationEdge
  field
    subject : Subject
    classifiedAs : Class
    evidence : Evidence
    revision : Revision

open ClassificationEdge public

classificationEdgePreservesSubject :
  ∀ {Subject Class Evidence Revision}
    (edge : ClassificationEdge Subject Class Evidence Revision) →
  subject edge ≡ subject edge
classificationEdgePreservesSubject edge = refl

------------------------------------------------------------------------
-- Recall after a lossy projection can depend on a prior/reconstruction rule.
-- This is a constructive witness of noncommutation rather than a universal
-- theorem asserting that every recall system drifts.
------------------------------------------------------------------------

record RecallProjectionNoncommutationWitness
    (Fine Coarse Prior : Set)
    (project : Fine → Coarse)
    (reconstruct : Coarse → Prior → Fine) : Set₁ where
  constructor recallProjectionNoncommutationWitness
  field
    original : Fine
    prior : Prior
    reconstructed : Fine
    reconstructedIsChosen : reconstructed ≡ reconstruct (project original) prior
    reconstructionDiffers : reconstructed ≡ original → ⊥

open RecallProjectionNoncommutationWitness public

------------------------------------------------------------------------
-- Future-cone diversity.
--
-- We keep the exact finite combinatorial quantity here: number of currently
-- live actions.  The Shannon effective-option count exp(H) belongs to a real /
-- transcendental analysis layer; this finite cardinal proxy needs no hidden
-- analytic postulates.
------------------------------------------------------------------------

FutureCone : Set → Set
FutureCone Action = List Action

optionCount : ∀ {Action} → FutureCone Action → Nat
optionCount [] = zero
optionCount (_ ∷ rest) = suc (optionCount rest)

reexpandOne : ∀ {Action} → Action → FutureCone Action → FutureCone Action
reexpandOne action cone = action ∷ cone

reexpandOneRaisesOptionCount :
  ∀ {Action} (action : Action) (cone : FutureCone Action) →
  optionCount (reexpandOne action cone) ≡ suc (optionCount cone)
reexpandOneRaisesOptionCount action cone = refl

------------------------------------------------------------------------
-- Protected provenance recovery: global inversion is unnecessary; what must
-- survive is an application-selected critical projection together with enough
-- receipt data to reconstruct the relevant state.
------------------------------------------------------------------------

record ProtectedProvenanceRecovery
    (State Surface Receipt Critical : Set)
    (project : State → Surface)
    (critical : State → Critical) : Set₁ where
  constructor protectedProvenanceRecovery
  field
    receipt : State → Receipt
    reopen : Surface → Receipt → State
    reopenCritical : ∀ state → critical (reopen (project state) (receipt state)) ≡ critical state

open ProtectedProvenanceRecovery public
