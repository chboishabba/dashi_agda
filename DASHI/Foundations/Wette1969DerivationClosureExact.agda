module DASHI.Foundations.Wette1969DerivationClosureExact where

------------------------------------------------------------------------
-- WETTE 1969 FINITE DERIVATION CLOSURE
--
-- This module strengthens the finite-context lane without introducing a new
-- trace engine.  Previously a rule application consumed premise-membership
-- evidence supplied externally.  Here we prove the generic closure facts that
-- let later premise evidence be generated from conclusions of earlier certified
-- applications in the same finite derivation context.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)
open import Data.Vec using (lookup)

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969InitialRuleTranscriptionExact as RuleBody
import DASHI.Foundations.Wette1969ProofCarryingRuleApplicationExact as Historical
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite

------------------------------------------------------------------------
-- Every certified rule application makes its conclusion available at the
-- reached context, definitionally modulo the TypedDependencyCore postcondition.
------------------------------------------------------------------------

certifiedConclusionAvailable :
  (context : Finite.DerivationContext) →
  (selected :
    PCRA.SelectedRuleApplication
      (Historical.historicalRuleApplicationSystem
        Finite.finiteHistoricalContextSystem)
      context) →
  Historical.Derives
    Finite.finiteHistoricalContextSystem
    (PCRA.applySelected
      (Historical.historicalRuleApplicationSystem
        Finite.finiteHistoricalContextSystem)
      selected)
    (RuleBody.conclusion (PCRA.selectedRule selected))
certifiedConclusionAvailable context selected
  rewrite Dependency.postcondition (PCRA.applicationProof selected) =
  Finite.newConclusionAvailable
    context
    (RuleBody.conclusion (PCRA.selectedRule selected))

------------------------------------------------------------------------
-- Every formula available before a certified step remains available after it.
------------------------------------------------------------------------

certifiedStepPreservesPriorFormula :
  (context : Finite.DerivationContext) →
  (selected :
    PCRA.SelectedRuleApplication
      (Historical.historicalRuleApplicationSystem
        Finite.finiteHistoricalContextSystem)
      context) →
  (formula : Signature.Formula) →
  Historical.Derives
    Finite.finiteHistoricalContextSystem context formula →
  Historical.Derives
    Finite.finiteHistoricalContextSystem
    (PCRA.applySelected
      (Historical.historicalRuleApplicationSystem
        Finite.finiteHistoricalContextSystem)
      selected)
    formula
certifiedStepPreservesPriorFormula context selected formula evidence
  rewrite Dependency.postcondition (PCRA.applicationProof selected) =
  Finite.oldFormulaRemainsAvailable
    context
    (RuleBody.conclusion (PCRA.selectedRule selected))
    formula
    evidence

------------------------------------------------------------------------
-- A later rule premise can be generated directly from an earlier conclusion
-- whenever the recovered historical formulae are equal.  This is the exact
-- closure seam needed to stop re-supplying such premise evidence externally.
------------------------------------------------------------------------

premiseFromPreviousCertifiedConclusion :
  (context : Finite.DerivationContext) →
  (previous :
    PCRA.SelectedRuleApplication
      (Historical.historicalRuleApplicationSystem
        Finite.finiteHistoricalContextSystem)
      context) →
  (later : RuleBody.HistoricalRuleBody) →
  (index : Fin (RuleBody.premiseCount later)) →
  lookup (RuleBody.premises later) index
    ≡ RuleBody.conclusion (PCRA.selectedRule previous) →
  Historical.Derives
    Finite.finiteHistoricalContextSystem
    (PCRA.applySelected
      (Historical.historicalRuleApplicationSystem
        Finite.finiteHistoricalContextSystem)
      previous)
    (lookup (RuleBody.premises later) index)
premiseFromPreviousCertifiedConclusion
  context previous later index equality
  rewrite equality =
  certifiedConclusionAvailable context previous

------------------------------------------------------------------------
-- Existing premise evidence can also be lifted wholesale through a certified
-- extension.  This is useful when a later historical rule reuses an earlier
-- premise family unchanged.
------------------------------------------------------------------------

premisesPersistAcrossCertifiedStep :
  (context : Finite.DerivationContext) →
  (selected :
    PCRA.SelectedRuleApplication
      (Historical.historicalRuleApplicationSystem
        Finite.finiteHistoricalContextSystem)
      context) →
  (later : RuleBody.HistoricalRuleBody) →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem context later →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem
    (PCRA.applySelected
      (Historical.historicalRuleApplicationSystem
        Finite.finiteHistoricalContextSystem)
      selected)
    later
premisesPersistAcrossCertifiedStep context selected later premises index =
  certifiedStepPreservesPriorFormula
    context selected
    (lookup (RuleBody.premises later) index)
    (premises index)

record Wette1969DerivationClosureBoundary : Set where
  constructor wette1969DerivationClosureBoundary
  field
    certifiedConclusionGeneratesLaterMembershipEvidence : Bool
    certifiedConclusionGeneratesLaterMembershipEvidenceIsTrue :
      certifiedConclusionGeneratesLaterMembershipEvidence ≡ true

    priorPremiseEvidencePersistsAcrossCertifiedExtension : Bool
    priorPremiseEvidencePersistsAcrossCertifiedExtensionIsTrue :
      priorPremiseEvidencePersistsAcrossCertifiedExtension ≡ true

    formulaEqualityStillRequiredToReuseConclusionAsSpecificPremise : Bool
    formulaEqualityStillRequiredToReuseConclusionAsSpecificPremiseIsTrue :
      formulaEqualityStillRequiredToReuseConclusionAsSpecificPremise ≡ true

    finiteClosureAlreadyDecidesAllHistoricalPremises : Bool
    finiteClosureAlreadyDecidesAllHistoricalPremisesIsFalse :
      finiteClosureAlreadyDecidesAllHistoricalPremises ≡ false

canonicalWette1969DerivationClosureBoundary :
  Wette1969DerivationClosureBoundary
canonicalWette1969DerivationClosureBoundary =
  wette1969DerivationClosureBoundary
    true refl
    true refl
    true refl
    false refl
