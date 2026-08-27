module DASHI.Core.ProofCarryingRuleApplicationExact where

------------------------------------------------------------------------
-- PROOF-CARRYING RULE APPLICATION
--
-- Cross-pollinated from the repository's proof-carrying admissible-control
-- pattern (notably FiniteAdmissibleCoding): a selected transition should carry
-- the evidence that makes it legal at the current state, rather than storing a
-- bare rule label and hoping legality is recovered later.
--
-- This owner is deliberately generic.  It says nothing about a particular
-- calculus, substitution algorithm, or semantics.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record RuleApplicationSystem : Set₁ where
  constructor ruleApplicationSystem
  field
    State : Set
    Rule : Set
    Applies : State → Rule → Set
    step : (state : State) → (rule : Rule) → Applies state rule → State

open RuleApplicationSystem public

------------------------------------------------------------------------
-- A selected rule is inseparable from its admissibility witness at the source.
------------------------------------------------------------------------

record SelectedRuleApplication
    (system : RuleApplicationSystem)
    (state : State system) : Set where
  constructor selectedRuleApplication
  field
    selectedRule : Rule system
    applicationProof : Applies system state selectedRule

open SelectedRuleApplication public

applySelected :
  (system : RuleApplicationSystem) →
  (state : State system) →
  SelectedRuleApplication system state →
  State system
applySelected system state selected =
  step system state
    (selectedRule selected)
    (applicationProof selected)

------------------------------------------------------------------------
-- Dependent finite traces: each later rule carries a proof at the state reached
-- by all earlier proof-carrying steps.
------------------------------------------------------------------------

data CertifiedRuleTrace
    (system : RuleApplicationSystem) : State system → Set₁ where
  done : ∀ {state} → CertifiedRuleTrace system state
  choose : ∀ {state}
    (selected : SelectedRuleApplication system state) →
    CertifiedRuleTrace system (applySelected system state selected) →
    CertifiedRuleTrace system state

runCertifiedTrace :
  (system : RuleApplicationSystem) →
  {state : State system} →
  CertifiedRuleTrace system state →
  State system
runCertifiedTrace system {state} done = state
runCertifiedTrace system {state} (choose selected rest) =
  runCertifiedTrace system rest

record ProofCarryingRuleApplicationBoundary : Set where
  constructor proofCarryingRuleApplicationBoundary
  field
    selectedRuleCarriesApplicationProof : Bool
    selectedRuleCarriesApplicationProofIsTrue :
      selectedRuleCarriesApplicationProof ≡ true

    laterTraceStepsAreIndexedByReachedState : Bool
    laterTraceStepsAreIndexedByReachedStateIsTrue :
      laterTraceStepsAreIndexedByReachedState ≡ true

    ruleLabelAloneImpliesAdmissibility : Bool
    ruleLabelAloneImpliesAdmissibilityIsFalse :
      ruleLabelAloneImpliesAdmissibility ≡ false

    proofCarryingApplicationAlreadyProvidesDomainSemantics : Bool
    proofCarryingApplicationAlreadyProvidesDomainSemanticsIsFalse :
      proofCarryingApplicationAlreadyProvidesDomainSemantics ≡ false

canonicalProofCarryingRuleApplicationBoundary :
  ProofCarryingRuleApplicationBoundary
canonicalProofCarryingRuleApplicationBoundary =
  proofCarryingRuleApplicationBoundary
    true refl
    true refl
    false refl
    false refl
