module DASHI.Foundations.Wette1969ProofCarryingRuleApplicationExact where

------------------------------------------------------------------------
-- WETTE 1969 PROOF-CARRYING HISTORICAL RULE APPLICATION
--
-- Eduard Wette,
-- "Definition eines (relativ vollständigen) formalen Systems konstruktiver
-- Arithmetik", Foundations of Mathematics, Springer 1969, pp. 130--195.
-- DOI: 10.1007/978-3-642-86745-3_9
--
-- Repo cross-pollination:
--   * TypedDependencyCore already owns DependentActionSystem and
--     AdmissibleAction;
--   * PR #610 uses that owner to enforce "admissibility before optimization";
--   * PR #221 carries admissibility proofs with selected controls.
--
-- The generic ProofCarryingRuleApplicationExact owner now reuses that substrate
-- directly.  This module instantiates it with Wette's historical rule bodies.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Fin using (Fin)
open import Data.Vec using (lookup)

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969InitialRuleTranscriptionExact as RuleBody
import DASHI.Foundations.Wette1969Rule9324x25PremiseTemplateExact as Rule9324x25

------------------------------------------------------------------------
-- Context interface.  `Derives` is deliberately abstract: later source work
-- may instantiate it by finite-context membership, closure under reconstructed
-- rules, or another historically justified notion.
------------------------------------------------------------------------

record HistoricalContextSystem : Set₁ where
  constructor historicalContextSystem
  field
    Context : Set
    Derives : Context → Signature.Formula → Set
    extend : Context → Signature.Formula → Context

open HistoricalContextSystem public

PremisesHold :
  (contexts : HistoricalContextSystem) →
  Context contexts →
  RuleBody.HistoricalRuleBody →
  Set
PremisesHold contexts context rule =
  (index : Fin (RuleBody.premiseCount rule)) →
  Derives contexts context (lookup (RuleBody.premises rule) index)

------------------------------------------------------------------------
-- Existing TypedDependencyCore substrate.
--
-- Precondition = every historical premise is available.
-- Postcondition = the resulting context is exactly extension by the historical
-- conclusion.  The proof-bearing AdmissibleAction therefore owns both legality
-- and the actual reached context.
------------------------------------------------------------------------

historicalRuleApplicationSystem :
  (contexts : HistoricalContextSystem) →
  PCRA.RuleApplicationSystem
    (Context contexts)
    RuleBody.HistoricalRuleBody
historicalRuleApplicationSystem contexts = record
  { Precondition = PremisesHold contexts
  ; Postcondition = λ before rule after →
      after ≡ extend contexts before (RuleBody.conclusion rule)
  ; actionLabel = λ rule → "Wette 1969 historical rule"
  }

certifyHistoricalRule :
  (contexts : HistoricalContextSystem) →
  (context : Context contexts) →
  (rule : RuleBody.HistoricalRuleBody) →
  PremisesHold contexts context rule →
  Dependency.AdmissibleAction
    (historicalRuleApplicationSystem contexts)
    context
    rule
certifyHistoricalRule contexts context rule premiseEvidence = record
  { precondition = premiseEvidence
  ; after = extend contexts context (RuleBody.conclusion rule)
  ; postcondition = refl
  ; dependencyReceipt = "all historical rule premises carried at source context"
  }

------------------------------------------------------------------------
-- 9.3.24 and 9.3.25 become selected proof-carrying transitions once their four
-- premise proofs are supplied at the current context.
------------------------------------------------------------------------

selectRule9324 :
  (contexts : HistoricalContextSystem) →
  (context : Context contexts) →
  (premises : Rule9324x25.Rule9324x25PremiseParameters) →
  (conclusions : Rule9324x25.Rule9324x25ConclusionParameters) →
  PremisesHold contexts context (Rule9324x25.rule9-3-24 premises conclusions) →
  PCRA.SelectedRuleApplication
    (historicalRuleApplicationSystem contexts)
    context
selectRule9324 contexts context premises conclusions evidence =
  PCRA.selectedRuleApplication
    (Rule9324x25.rule9-3-24 premises conclusions)
    (certifyHistoricalRule contexts context
      (Rule9324x25.rule9-3-24 premises conclusions)
      evidence)

selectRule9325 :
  (contexts : HistoricalContextSystem) →
  (context : Context contexts) →
  (premises : Rule9324x25.Rule9324x25PremiseParameters) →
  (conclusions : Rule9324x25.Rule9324x25ConclusionParameters) →
  PremisesHold contexts context (Rule9324x25.rule9-3-25 premises conclusions) →
  PCRA.SelectedRuleApplication
    (historicalRuleApplicationSystem contexts)
    context
selectRule9325 contexts context premises conclusions evidence =
  PCRA.selectedRuleApplication
    (Rule9324x25.rule9-3-25 premises conclusions)
    (certifyHistoricalRule contexts context
      (Rule9324x25.rule9-3-25 premises conclusions)
      evidence)

applyRule9324ExtendsByHistoricalConclusion :
  (contexts : HistoricalContextSystem) →
  (context : Context contexts) →
  (premises : Rule9324x25.Rule9324x25PremiseParameters) →
  (conclusions : Rule9324x25.Rule9324x25ConclusionParameters) →
  (evidence :
    PremisesHold contexts context (Rule9324x25.rule9-3-24 premises conclusions)) →
  PCRA.applySelected
    (historicalRuleApplicationSystem contexts)
    (selectRule9324 contexts context premises conclusions evidence)
  ≡ extend contexts context (Rule9324x25.rule9-3-24Conclusion conclusions)
applyRule9324ExtendsByHistoricalConclusion
  contexts context premises conclusions evidence = refl

applyRule9325ExtendsByHistoricalConclusion :
  (contexts : HistoricalContextSystem) →
  (context : Context contexts) →
  (premises : Rule9324x25.Rule9324x25PremiseParameters) →
  (conclusions : Rule9324x25.Rule9324x25ConclusionParameters) →
  (evidence :
    PremisesHold contexts context (Rule9324x25.rule9-3-25 premises conclusions)) →
  PCRA.applySelected
    (historicalRuleApplicationSystem contexts)
    (selectRule9325 contexts context premises conclusions evidence)
  ≡ extend contexts context (Rule9324x25.rule9-3-25Conclusion conclusions)
applyRule9325ExtendsByHistoricalConclusion
  contexts context premises conclusions evidence = refl

record Wette1969ProofCarryingApplicationBoundary : Set where
  constructor wette1969ProofCarryingApplicationBoundary
  field
    typedDependencyCoreReusedForHistoricalAdmissibility : Bool
    typedDependencyCoreReusedForHistoricalAdmissibilityIsTrue :
      typedDependencyCoreReusedForHistoricalAdmissibility ≡ true

    historicalRuleSelectionCarriesAllPremiseEvidence : Bool
    historicalRuleSelectionCarriesAllPremiseEvidenceIsTrue :
      historicalRuleSelectionCarriesAllPremiseEvidence ≡ true

    rules9324And9325NowLiftToCertifiedContextTransitions : Bool
    rules9324And9325NowLiftToCertifiedContextTransitionsIsTrue :
      rules9324And9325NowLiftToCertifiedContextTransitions ≡ true

    bareHistoricalRuleBodyIsAlreadyAdmissibleAtEveryContext : Bool
    bareHistoricalRuleBodyIsAlreadyAdmissibleAtEveryContextIsFalse :
      bareHistoricalRuleBodyIsAlreadyAdmissibleAtEveryContext ≡ false

    contextPremiseEvidenceIsAlreadyArithmeticSoundness : Bool
    contextPremiseEvidenceIsAlreadyArithmeticSoundnessIsFalse :
      contextPremiseEvidenceIsAlreadyArithmeticSoundness ≡ false

    certifiedContextTransitionAlreadyImplementsHistoricalSubstitution : Bool
    certifiedContextTransitionAlreadyImplementsHistoricalSubstitutionIsFalse :
      certifiedContextTransitionAlreadyImplementsHistoricalSubstitution ≡ false

canonicalWette1969ProofCarryingApplicationBoundary :
  Wette1969ProofCarryingApplicationBoundary
canonicalWette1969ProofCarryingApplicationBoundary =
  wette1969ProofCarryingApplicationBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
