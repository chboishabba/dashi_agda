module DASHI.Foundations.Wette1969DerivationClosureExact where

------------------------------------------------------------------------
-- WETTE 1969 FINITE DERIVATION CLOSURE
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

historicalApplicationSystem :
  PCRA.RuleApplicationSystem
    Finite.DerivationContext
    RuleBody.HistoricalRuleBody
historicalApplicationSystem =
  Historical.historicalRuleApplicationSystem
    Finite.finiteHistoricalContextSystem

certifiedConclusionAvailable :
  (context : Finite.DerivationContext) →
  (selected : PCRA.SelectedRuleApplication historicalApplicationSystem context) →
  Historical.Derives
    Finite.finiteHistoricalContextSystem
    (PCRA.applySelected historicalApplicationSystem selected)
    (RuleBody.conclusion (PCRA.selectedRule selected))
certifiedConclusionAvailable context selected
  rewrite Dependency.postcondition (PCRA.applicationProof selected) =
  Finite.newConclusionAvailable
    context
    (RuleBody.conclusion (PCRA.selectedRule selected))

certifiedStepPreservesPriorFormula :
  (context : Finite.DerivationContext) →
  (selected : PCRA.SelectedRuleApplication historicalApplicationSystem context) →
  (formula : Signature.Formula) →
  Historical.Derives
    Finite.finiteHistoricalContextSystem context formula →
  Historical.Derives
    Finite.finiteHistoricalContextSystem
    (PCRA.applySelected historicalApplicationSystem selected)
    formula
certifiedStepPreservesPriorFormula context selected formula evidence
  rewrite Dependency.postcondition (PCRA.applicationProof selected) =
  Finite.oldFormulaRemainsAvailable
    context
    (RuleBody.conclusion (PCRA.selectedRule selected))
    formula
    evidence

premiseFromPreviousCertifiedConclusion :
  (context : Finite.DerivationContext) →
  (previous : PCRA.SelectedRuleApplication historicalApplicationSystem context) →
  (later : RuleBody.HistoricalRuleBody) →
  (index : Fin (RuleBody.premiseCount later)) →
  lookup (RuleBody.premises later) index
    ≡ RuleBody.conclusion (PCRA.selectedRule previous) →
  Historical.Derives
    Finite.finiteHistoricalContextSystem
    (PCRA.applySelected historicalApplicationSystem previous)
    (lookup (RuleBody.premises later) index)
premiseFromPreviousCertifiedConclusion
  context previous later index equality
  rewrite equality =
  certifiedConclusionAvailable context previous

premisesPersistAcrossCertifiedStep :
  (context : Finite.DerivationContext) →
  (selected : PCRA.SelectedRuleApplication historicalApplicationSystem context) →
  (later : RuleBody.HistoricalRuleBody) →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem context later →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem
    (PCRA.applySelected historicalApplicationSystem selected)
    later
premisesPersistAcrossCertifiedStep context selected later premises index =
  certifiedStepPreservesPriorFormula
    context selected
    (lookup (RuleBody.premises later) index)
    (premises index)

certifiedTracePreservesPriorFormula :
  {context : Finite.DerivationContext} →
  (trace : PCRA.CertifiedRuleTrace historicalApplicationSystem context) →
  (formula : Signature.Formula) →
  Historical.Derives
    Finite.finiteHistoricalContextSystem context formula →
  Historical.Derives
    Finite.finiteHistoricalContextSystem
    (PCRA.runCertifiedTrace historicalApplicationSystem trace)
    formula
certifiedTracePreservesPriorFormula PCRA.done formula evidence = evidence
certifiedTracePreservesPriorFormula
  {context}
  (PCRA.choose selected rest)
  formula
  evidence =
  certifiedTracePreservesPriorFormula
    rest
    formula
    (certifiedStepPreservesPriorFormula context selected formula evidence)

headConclusionAvailableAtTraceTarget :
  {context : Finite.DerivationContext} →
  (selected : PCRA.SelectedRuleApplication historicalApplicationSystem context) →
  (rest :
    PCRA.CertifiedRuleTrace
      historicalApplicationSystem
      (PCRA.applySelected historicalApplicationSystem selected)) →
  Historical.Derives
    Finite.finiteHistoricalContextSystem
    (PCRA.runCertifiedTrace historicalApplicationSystem rest)
    (RuleBody.conclusion (PCRA.selectedRule selected))
headConclusionAvailableAtTraceTarget {context} selected rest =
  certifiedTracePreservesPriorFormula
    rest
    (RuleBody.conclusion (PCRA.selectedRule selected))
    (certifiedConclusionAvailable context selected)

premisesPersistAcrossCertifiedTrace :
  {context : Finite.DerivationContext} →
  (trace : PCRA.CertifiedRuleTrace historicalApplicationSystem context) →
  (later : RuleBody.HistoricalRuleBody) →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem context later →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem
    (PCRA.runCertifiedTrace historicalApplicationSystem trace)
    later
premisesPersistAcrossCertifiedTrace trace later premises index =
  certifiedTracePreservesPriorFormula
    trace
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

    priorFormulaePersistAcrossWholeCertifiedTrace : Bool
    priorFormulaePersistAcrossWholeCertifiedTraceIsTrue :
      priorFormulaePersistAcrossWholeCertifiedTrace ≡ true

    earlierCertifiedConclusionsPersistToTraceTarget : Bool
    earlierCertifiedConclusionsPersistToTraceTargetIsTrue :
      earlierCertifiedConclusionsPersistToTraceTarget ≡ true

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
    true refl
    true refl
    false refl
