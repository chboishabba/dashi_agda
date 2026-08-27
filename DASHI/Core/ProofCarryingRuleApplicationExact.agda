module DASHI.Core.ProofCarryingRuleApplicationExact where

------------------------------------------------------------------------
-- PROOF-CARRYING RULE APPLICATION
--
-- Repo-native extraction of a pattern already present in two places:
--
--   * TypedDependencyCore owns DependentActionSystem / AdmissibleAction;
--   * PR #221's FiniteAdmissibleCoding makes selected controls carry their
--     admissibility proof.
--
-- A formal-rule application is therefore represented as an ordinary dependent
-- action.  This module adds only the calculus-facing naming and the dependent
-- finite-trace carrier; it does not introduce a parallel admissibility system.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TypedDependencyCore as Dependency

RuleApplicationSystem : Set → Set → Set₁
RuleApplicationSystem State Rule = Dependency.DependentActionSystem State Rule

RuleApplication :
  {State Rule : Set} →
  RuleApplicationSystem State Rule → State → Rule → Set
RuleApplication = Dependency.AdmissibleAction

------------------------------------------------------------------------
-- A selected rule is exactly a rule label paired with an existing
-- TypedDependencyCore admissibility witness.
------------------------------------------------------------------------

record SelectedRuleApplication
    {State Rule : Set}
    (system : RuleApplicationSystem State Rule)
    (state : State) : Set where
  constructor selectedRuleApplication
  field
    selectedRule : Rule
    applicationProof : Dependency.AdmissibleAction system state selectedRule

open SelectedRuleApplication public

applySelected :
  {State Rule : Set} →
  (system : RuleApplicationSystem State Rule) →
  {state : State} →
  SelectedRuleApplication system state →
  State
applySelected system selected =
  Dependency.after (applicationProof selected)

------------------------------------------------------------------------
-- Dependent finite traces: each later rule carries an admissibility witness at
-- the state reached by all earlier proof-carrying applications.
------------------------------------------------------------------------

data CertifiedRuleTrace
    {State Rule : Set}
    (system : RuleApplicationSystem State Rule) : State → Set₁ where
  done : ∀ {state} → CertifiedRuleTrace system state
  choose : ∀ {state}
    (selected : SelectedRuleApplication system state) →
    CertifiedRuleTrace system (applySelected system selected) →
    CertifiedRuleTrace system state

runCertifiedTrace :
  {State Rule : Set} →
  (system : RuleApplicationSystem State Rule) →
  {state : State} →
  CertifiedRuleTrace system state →
  State
runCertifiedTrace system {state} done = state
runCertifiedTrace system (choose selected rest) =
  runCertifiedTrace system rest

record ProofCarryingRuleApplicationBoundary : Set where
  constructor proofCarryingRuleApplicationBoundary
  field
    typedDependencyCoreOwnsAdmissibility : Bool
    typedDependencyCoreOwnsAdmissibilityIsTrue :
      typedDependencyCoreOwnsAdmissibility ≡ true

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
    true refl
    false refl
    false refl
