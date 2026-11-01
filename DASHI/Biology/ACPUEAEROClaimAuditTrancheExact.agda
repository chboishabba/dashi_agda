module DASHI.Biology.ACPUEAEROClaimAuditTrancheExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.ClaimAuditManifestExact as Manifest
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as Design
import DASHI.Biology.ACPUEAEROClaimAuditProtocolExact as Protocol

------------------------------------------------------------------------
-- FIRST SOURCE-RECOVERED CLAIM-AUDIT TRANCHE
--
-- This file contains real AERO/source surfaces, but does NOT invent an ACPUE
-- row code where the interactive table row has not yet been recovered through
-- the available crawler.  ACPUE coding and DASHI independent coding therefore
-- remain explicitly separate.
--
-- AERO 2023 PDF, Purpose and approach, pp. 7-8 (PDF pages 6-7 in zero-based
-- tooling):
--   "To identify the most effective teaching practices, AERO has drawn on
--    evidence that shows consistent positive impact on learning outcomes for
--    students across diverse contexts (Gonsalkorale, 2022)."
--
-- Cited source recovered:
-- Karen Gonsalkorale, AERO, 27 September 2022,
-- "'But that would never work here' – Does context matter more than evidence?"
-- The article reports an AERO evidence review of meta-analytic reviews for
-- THREE practices: formative assessment, explicit instruction and mastery
-- learning; it says they are effective across a variety of contexts/subgroups
-- and are likely to work in a variety of classrooms.
------------------------------------------------------------------------

claim001Scope : PNF.AssertionScope
claim001Scope =
  PNF.assertionScope
    "students represented by the diverse contexts invoked in the cited synthesis"
    "diverse school/classroom contexts"
    "teaching practices selected as most effective"
    "other teaching practices or baseline practice"
    "learning outcomes"
    "unspecified in the overview sentence"

claim001Predicates : List PNF.PredicateAtom
claim001Predicates =
  PNF.predicateAtom
    "positive-impact"
    PNF.outcomePredicate
    "practice × student × learning outcome × context"
    "the nominated practice has a positive impact on student learning outcomes"
  ∷ PNF.predicateAtom
    "across-diverse-contexts"
    PNF.transportPredicate
    "source contexts × target contexts"
    "positive impact is sufficiently stable across diverse contexts to support transport"
  ∷ PNF.predicateAtom
    "most-effective"
    PNF.significancePredicate
    "candidate teaching practices × comparator set"
    "the evidence warrants the comparative phrase most effective, not merely positive effect"
  ∷ []

claim001Assertion : PNF.PredicateNormalAssertion
claim001Assertion =
  PNF.predicateNormalAssertion
    "AERO-HSLB-PURPOSE-GONSALKORALE-001"
    "To identify the most effective teaching practices, AERO has drawn on evidence that shows consistent positive impact on learning outcomes for students across diverse contexts (Gonsalkorale, 2022)."
    PNF.boundedUniversalQ
    PNF.comparativeF
    claim001Scope
    claim001Predicates
    "AERO, How students learn best (2023), Purpose and approach, PDF p. 8; Gonsalkorale (2022) citation"

claim001LocalEffectObligation : PNF.AssertionObligation
claim001LocalEffectObligation =
  PNF.assertionObligation
    "AERO-HSLB-PURPOSE-GONSALKORALE-001"
    PNF.predicateContentObligation
    "Does Gonsalkorale 2022 support positive learning-outcome effects for the teaching practices actually reviewed?"

claim001TransportObligation : PNF.AssertionObligation
claim001TransportObligation =
  PNF.assertionObligation
    "AERO-HSLB-PURPOSE-GONSALKORALE-001"
    PNF.transportObligation
    "How far does the reviewed cross-context evidence warrant transport beyond the specific practices, subjects, year levels and subgroups represented?"

claim001ComparativeObligation : PNF.AssertionObligation
claim001ComparativeObligation =
  PNF.assertionObligation
    "AERO-HSLB-PURPOSE-GONSALKORALE-001"
    PNF.practicalSignificanceObligation
    "Does the source establish the comparative superlative most effective rather than positive/effective across the reviewed contexts?"

claim001Design : Design.StudyDesignReceipt
claim001Design =
  Design.studyDesignReceipt
    "Gonsalkorale-2022-AERO-context-article"
    Design.practitionerSynthesis
    "article summarises an AERO evidence review of meta-analytic reviews across locations, year levels, subjects and subgroups"
    "not a newly randomised allocation in the article"
    "varies by underlying reviews; article compares applicability across contexts, not a complete tournament of all teaching practices"
    "depends on underlying meta-analytic reviews; not independently re-estimated in the article"
    "not applicable as a single participant-flow trial"
    "depends on underlying reviews"
    "not an implementation-fidelity trial at article level"
    "depends on underlying reviews"
    "article reports direction/positive impact, not one common effect-size surface"
    "article-level uncertainty intervals are not exposed in the cited prose"
    "three practices across reported subjects, primary/secondary groups and additional-learning-needs subgroups"
    Design.informant
    Design.validityUnassessed
    Design.validityModerate
    "Karen Gonsalkorale, AERO, 27 September 2022, 'But that would never work here' – Does context matter more than evidence?"

claim001Evidence : Design.EvidenceReceipt
claim001Evidence =
  Design.evidenceReceipt
    "Gonsalkorale-2022-article-recovered"
    claim001Design
    "Karen Gonsalkorale (AERO), 27 September 2022"
    "The article reports that formative assessment, explicit instruction and mastery learning are effective across a variety of contexts/subgroups and concludes they are likely to work in a variety of classrooms."
    "direct source recovery and bounded prose comparison"
    "AERO overview sentence -> cited Gonsalkorale article -> article's summary of underlying meta-analytic reviews; primary/meta-analysis chain remains to be audited separately"
    "independent DASHI audit interpretation; not attributed to ACPUE or AERO"
    "article is a secondary/agency synthesis; source-level prose does not expose one exhaustive comparator set establishing a global most-effective ranking"

claim001ObligationAudits : List PNF.ObligationAudit
claim001ObligationAudits =
  PNF.obligationAudit
    claim001LocalEffectObligation
    PNF.discharged
    "Gonsalkorale 2022 reports positive impacts for the three reviewed practices across multiple reported contexts/subgroups"
    "bounded predicate support is present for the practices actually reviewed"
  ∷ PNF.obligationAudit
    claim001TransportObligation
    PNF.partiallyDischarged
    "source says variety of contexts/classrooms and reports primary/secondary and subgroup coverage"
    "cross-context support exists, but the source wording is variety/broad relevance rather than an unrestricted transport theorem"
  ∷ PNF.obligationAudit
    claim001ComparativeObligation
    PNF.unresolved
    "no complete all-practices comparator/tournament is exposed in the cited article prose"
    "positive effect across contexts does not by itself discharge the superlative most-effective predicate"
  ∷ []

claim001SafeScope : PNF.AssertionScope
claim001SafeScope =
  PNF.assertionScope
    "primary and secondary students/subgroups represented in the reviewed evidence"
    "the variety of contexts represented in the reviewed evidence"
    "formative assessment, explicit instruction and mastery learning"
    "comparators in the underlying reviews"
    "student achievement/learning outcomes reported by the reviews"
    "as represented in the evidence synthesised by the 2022 article"

claim001SafePredicates : List PNF.PredicateAtom
claim001SafePredicates =
  PNF.predicateAtom
    "positive-impact-in-reviewed-contexts"
    PNF.outcomePredicate
    "three reviewed practices × represented contexts"
    "the cited synthesis reports positive learning/achievement impacts for the three reviewed practices across varied represented contexts"
  ∷ []

claim001BackwardSafeAssertion : PNF.PredicateNormalAssertion
claim001BackwardSafeAssertion =
  PNF.predicateNormalAssertion
    "AERO-HSLB-PURPOSE-GONSALKORALE-001-SAFE"
    "The cited AERO synthesis reports positive effects for formative assessment, explicit instruction and mastery learning across a variety of the contexts and student subgroups represented in its reviewed evidence."
    PNF.studyPopulationQ
    PNF.descriptiveF
    claim001SafeScope
    claim001SafePredicates
    "DASHI backward-safe reconstruction from the recovered cited-source prose; not a quotation or ACPUE judgement"

claim001SourceChain : List Manifest.SourceChainCoordinate
claim001SourceChain =
  Manifest.sourceChainCoordinate
    Manifest.publishedSurface
    "AERO How students learn best (2023), Purpose and approach, PDF p. 8"
    true
    "exact AERO sentence recovered"
  ∷ Manifest.sourceChainCoordinate
    Manifest.citedSecondarySource
    "Karen Gonsalkorale, AERO article, 27 September 2022"
    true
    "cited agency synthesis recovered"
  ∷ Manifest.sourceChainCoordinate
    Manifest.citedPrimaryStudy
    "underlying meta-analytic reviews and their included primary studies"
    false
    "next BIDI depth: recover the exact reviews/studies and their context/effect estimates"
  ∷ Manifest.sourceChainCoordinate
    Manifest.underlyingDatasetOrArtifact
    "underlying review extraction tables / primary-study data"
    false
    "not yet recovered"
  ∷ []

claim001Receipts : List Manifest.TypedClaimReceipt
claim001Receipts =
  Manifest.typedClaimReceipt
    Manifest.predicateContentReceipt
    Manifest.installed
    "Gonsalkorale 2022 article"
    "bounded to three reviewed practices and the contexts/subgroups described"
  ∷ Manifest.typedClaimReceipt
    Manifest.transportReceipt
    Manifest.partiallyInstalled
    "cross-context synthesis language"
    "variety of contexts is not encoded as unrestricted all-context transport"
  ∷ Manifest.typedClaimReceipt
    Manifest.practicalSignificanceReceipt
    Manifest.unresolved
    "global most-effective comparator not recovered from article prose"
    "requires explicit comparator/effect synthesis before superlative promotion"
  ∷ []

claim001Manifest : Manifest.ManifestClaim
claim001Manifest =
  Manifest.manifestClaim
    "AERO-HSLB-PURPOSE-GONSALKORALE-001"
    ""
    (PNF.naturalLanguage claim001Assertion)
    claim001Assertion
    (Manifest.comparativeConsequence ∷ Manifest.downstreamPolicyRelevant ∷ [])
    claim001SourceChain
    claim001Receipts
    claim001ObligationAudits
    Manifest.independentUnresolved
    Manifest.independentPartiallyAdmissible
    Manifest.citationCompared
    claim001BackwardSafeAssertion
    "Provisional independent audit. ACPUE row coding is intentionally unresolved until the exact interactive-table row is recovered. The cited source supports bounded positive-effect/context predicates while transport breadth and the comparative superlative remain separate obligations."

claim001ProtocolCandidate : Protocol.AuditCandidate
claim001ProtocolCandidate =
  Protocol.auditCandidate
    "AERO-HSLB-PURPOSE-GONSALKORALE-001"
    (PNF.naturalLanguage claim001Assertion)
    "AERO 2023 PDF p. 8, Purpose and approach"
    Protocol.acpueCodeNotYetRecovered
    Protocol.practitionerOrAgencySynthesis
    (Protocol.transportClaim ∷ Protocol.comparativeBestClaim ∷ [])
    (Manifest.comparativeConsequence ∷ Manifest.downstreamPolicyRelevant ∷ [])
    Protocol.highConsequencePriority
    "high-value calibration of positive-effect evidence versus comparative and transport amplification"

record Claim001Boundary : Set where
  constructor claim001Boundary
  field
    articlePositiveEffectEqualsGlobalBestRanking : Bool
    varietyOfContextsEqualsAllContexts : Bool
    acpueCodeInventedBeforeRecovery : Bool
    boundedPredicateSupportRetained : Bool
    backwardSafeRewriteInstalled : Bool
    primaryEvidenceChainComplete : Bool

canonicalClaim001Boundary : Claim001Boundary
canonicalClaim001Boundary =
  claim001Boundary false false false true true false
