module DASHI.Governance.TraumaWeightingTerminalisationLift where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Trauma-like provenance-to-action transfer.
--
-- This is a structural dynamical analogy, not a clinical diagnosis of a
-- polity, institution, nation or public actor.  The same dynamical form does
-- not imply the same psychological mechanism.
------------------------------------------------------------------------

record ProvenanceActionDynamics : Set₁ where
  field
    State : Set
    Provenance : Set
    Evidence : Set
    Action : Set
    Gain : Set

    provenance : State → Provenance
    gain : State → Gain
    choose : State → Evidence → Action
    update : State → Evidence → State

open ProvenanceActionDynamics public

record TraumaLikeWeighting (D : ProvenanceActionDynamics) : Set₁ where
  field
    state : State D
    HighHistoricalGain : Set
    highHistoricalGain : HighHistoricalGain
    RestrictedFutureCone : Set
    restrictedFutureCone : RestrictedFutureCone

open TraumaLikeWeighting public

------------------------------------------------------------------------
-- Corrective learning and terminalisation are independent.
------------------------------------------------------------------------

record CorrectiveGainRevision (D : ProvenanceActionDynamics) : Set₁ where
  field
    state : State D
    counterevidence : Evidence D
    GainReduced : Gain D → Gain D → Set
    gainReduced : GainReduced (gain D state) (gain D (update D state counterevidence))

open CorrectiveGainRevision public

record TerminalisedGain (D : ProvenanceActionDynamics) : Set₁ where
  field
    state : State D
    Counterevidence : Set
    counterevidenceAsEvidence : Counterevidence → Evidence D
    GainCannotReduce : Gain D → Gain D → Set
    locked :
      (e : Counterevidence) →
      GainCannotReduce
        (gain D state)
        (gain D (update D state (counterevidenceAsEvidence e)))

open TerminalisedGain public

------------------------------------------------------------------------
-- A high historical gain is not terminalisation: a constructive corrective
-- revision witness can coexist with trauma-like weighting.
------------------------------------------------------------------------

record HighGainButRevisable (D : ProvenanceActionDynamics) : Set₁ where
  field
    weighting : TraumaLikeWeighting D
    revision : CorrectiveGainRevision D

open HighGainButRevisable public

------------------------------------------------------------------------
-- Memory preservation and action-policy revision are deliberately separate.
------------------------------------------------------------------------

record MemoryActionDecoupling : Set₁ where
  field
    Event : Set
    Memory : Set
    Action : Set
    remember : Event → Memory
    actFrom : Memory → Action
    reviseAction : Memory → Action

open MemoryActionDecoupling public

record PreservedMemoryRevisedAction (M : MemoryActionDecoupling) : Set₁ where
  field
    event : Event M
    memoryPreserved : remember M event ≡ remember M event
    ActionChanged : Action M → Action M → Set
    actionChanged : ActionChanged (actFrom M (remember M event)) (reviseAction M (remember M event))

open PreservedMemoryRevisedAction public

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

data StructuralTraumaAnalogyIsClinicalDiagnosis : Set where

structuralAnalogyDoesNotDiagnose :
  StructuralTraumaAnalogyIsClinicalDiagnosis → ⊥
structuralAnalogyDoesNotDiagnose ()
