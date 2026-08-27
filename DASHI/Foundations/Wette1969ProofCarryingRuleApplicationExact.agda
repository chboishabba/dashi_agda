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
--   PR #221's FiniteAdmissibleCoding carries an admissibility proof together
--   with every selected control.  The generic
--   DASHI.Core.ProofCarryingRuleApplicationExact owner extracts that pattern
--   for formal calculi.  This module applies it to Wette's typed historical
--   rule bodies.
--
-- A historical rule body is not itself an executable transition.  Application
-- requires evidence that every premise is available/derivable in the current
-- context.  The result state is then obtained by extending that context with
-- the rule conclusion.  No semantic truth or substitution evaluator is
-- manufactured here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)
open import Data.Vec using (lookup)

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969InitialRuleTranscriptionExact as RuleBody
import DASHI.Foundations.Wette1969Rule9324x25PremiseTemplateExact as Rule9324x25

------------------------------------------------------------------------
-- Context interface.  `Derives` is intentionally abstract: a later historical
-- reconstruction may instantiate it by membership in a finite derivation state,
-- closure under already reconstructed rules, or another source-justified
-- notion.  This module needs only premise evidence and conclusion extension.
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

historicalRuleApplicationSystem :
  HistoricalContextSystem → PCRA.RuleApplicationSystem
historicalRuleApplicationSystem contexts =
  PCRA.ruleApplicationSystem
    (Context contexts)
    RuleBody.HistoricalRuleBody
    (PremisesHold contexts)
    apply
  where
    apply :
      (context : Context contexts) →
      (rule : RuleBody.HistoricalRuleBody) →
      PremisesHold contexts context rule →
      Context contexts
    apply context rule premiseEvidence =
      extend contexts context (RuleBody.conclusion rule)

------------------------------------------------------------------------
-- 9.3.24 and 9.3.25 become genuine selected proof-carrying transitions once
-- their four premise proofs are supplied at a context.
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
    evidence

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
    evidence

------------------------------------------------------------------------
-- Applying either selected rule extends the context by its historical
-- conclusion.  These equalities are definitional regression receipts.
------------------------------------------------------------------------

applyRule9324ExtendsByHistoricalConclusion :
  (contexts : HistoricalContextSystem) →
  (context : Context contexts) →
  (premises : Rule9324x25.Rule9324x25PremiseParameters) →
  (conclusions : Rule9324x25.Rule9324x25ConclusionParameters) →
  (evidence :
    PremisesHold contexts context (Rule9324x25.rule9-3-24 premises conclusions)) →
  PCRA.applySelected
    (historicalRuleApplicationSystem contexts)
    context
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
    context
    (selectRule9325 contexts context premises conclusions evidence)
  ≡ extend contexts context (Rule9324x25.rule9-3-25Conclusion conclusions)
applyRule9325ExtendsByHistoricalConclusion
  contexts context premises conclusions evidence = refl

record Wette1969ProofCarryingApplicationBoundary : Set where
  constructor wette1969ProofCarryingApplicationBoundary
  field
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
    false refl
    false refl
    false refl
