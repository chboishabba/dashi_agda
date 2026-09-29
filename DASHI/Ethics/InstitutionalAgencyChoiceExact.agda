module DASHI.Ethics.InstitutionalAgencyChoiceExact where

-- DASHI reconstruction, NOT a theorem of Forrest Landry or Rob McNamara.
-- Source attribution: see InstitutionalAgencySourceAtlas.
-- Distinguishes nominally offered options from effectively viable options.
-- No assertion here establishes coercion, illegality, or physical free will.

open import DASHI.Core.Prelude

record ChoiceEnvironment : Set₁ where
  field
    Agent  : Set
    State  : Set
    Action : Set
    offered : Agent → State → Action → Set
    viable  : Agent → State → Action → Set
    viability-sound :
      ∀ a s x → viable a s x → offered a s x

open ChoiceEnvironment

Nominal : (E : ChoiceEnvironment) →
  Agent E → State E → Set
Nominal E a s = Σ (Action E) (offered E a s)

Feasible : (E : ChoiceEnvironment) →
  Agent E → State E → Set
Feasible E a s = Σ (Action E) (viable E a s)

feasible-to-nominal :
  (E : ChoiceEnvironment) →
  (a : Agent E) → (s : State E) →
  Feasible E a s → Nominal E a s
feasible-to-nominal E a s (x , proof) =
  x , viability-sound E a s x proof

-- A small constructive countermodel: nominal alternatives exist, but
-- the only viable option is acceptance. This does not model legal consent.
data ContractOption : Set where
  accept reject : ContractOption

data SingleAgent : Set where
  applicant : SingleAgent

data SingleState : Set where
  offeredTerms : SingleState

offeredOption : SingleAgent → SingleState → ContractOption → Set
offeredOption _ _ _ = ⊤

viableOption : SingleAgent → SingleState → ContractOption → Set
viableOption _ _ accept = ⊤
viableOption _ _ reject = ⊥

choiceExample : ChoiceEnvironment
choiceExample = record
  { Agent = SingleAgent
  ; State = SingleState
  ; Action = ContractOption
  ; offered = offeredOption
  ; viable = viableOption
  ; viability-sound = λ _ _ { accept p → tt ; reject () }
  }

acceptOffered : offered choiceExample applicant offeredTerms accept
acceptOffered = tt

rejectOffered : offered choiceExample applicant offeredTerms reject
rejectOffered = tt

acceptFeasible : viable choiceExample applicant offeredTerms accept
acceptFeasible = tt

rejectNotFeasible : ¬ (viable choiceExample applicant offeredTerms reject)
rejectNotFeasible ()

allFeasibleAreAcceptance :
  (x : ContractOption) →
  viable choiceExample applicant offeredTerms x →
  x ≡ accept
allFeasibleAreAcceptance accept _ = refl
allFeasibleAreAcceptance reject ()

-- Resource-dependency predicates are explicit INPUTS, not inferred from
-- a source citation or the existence of non-negotiable terms.
record InstitutionalDependency : Set₁ where
  field
    Agent Institution Resource Goal : Set
    controls : Institution → Resource → Set
    depends : Agent → Resource → Goal → Set

StructuralPower :
  (D : InstitutionalDependency) →
  InstitutionalDependency.Institution D →
  InstitutionalDependency.Agent D →
  InstitutionalDependency.Goal D → Set
StructuralPower D institution agent goal =
  Σ (InstitutionalDependency.Resource D)
    (λ resource →
      InstitutionalDependency.controls D institution resource ×
      InstitutionalDependency.depends D agent resource goal)
