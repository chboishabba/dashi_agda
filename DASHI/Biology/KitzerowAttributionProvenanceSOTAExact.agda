module DASHI.Biology.KitzerowAttributionProvenanceSOTAExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- SURROUNDING SOTA / INSTITUTIONAL GUIDANCE FOR PROVENANCE AND ATTRIBUTION
--
-- These sources constrain vocabulary and evidence handling. They do not
-- adjudicate any Kitzerow comparison, establish legal liability, or transfer
-- institutional authority to DASHI.
------------------------------------------------------------------------

oriResearchMisconductDefinition : Source.AttributedSource
oriResearchMisconductDefinition =
  Source.mkNoDOISource
    "U.S. Office of Research Integrity"
    "Definition of Research Misconduct"
    "ORI / HHS"
    "current page inspected 2026"
    "https://ori.hhs.gov/definition-research-misconduct"
    Source.governmentSource
    "Federal/PHS research-misconduct vocabulary: plagiarism is appropriation of another person's ideas, processes, results or words without appropriate credit; honest error and differences of opinion are excluded. Scope and adjudicatory requirements remain those of the source regime."
    Source.publicAttribution

copePlagiarismFlowchart : Source.AttributedSource
copePlagiarismFlowchart =
  Source.mkDOISource
    "COPE Council"
    "Plagiarism in a published article — COPE flowchart"
    "Committee on Publication Ethics"
    "2021"
    "10.24318/cope.2019.2.2"
    "https://publicationethics.org/files/plagiarism-published-article-cope-flowchart.pdf"
    Source.institutionalSource
    "Publication-ethics investigative guidance requiring documentary evidence and distinguishing degrees/types of copying; it guides evidence handling but does not itself adjudicate a Kitzerow claim."
    Source.publicAttribution

copeRedundantPublicationFlowchart : Source.AttributedSource
copeRedundantPublicationFlowchart =
  Source.mkDOISource
    "COPE Council"
    "Redundant (duplicate) publication in a published article — COPE flowchart"
    "Committee on Publication Ethics"
    "2025"
    "10.24318/cope.2019.2.13"
    "https://publicationethics.org/sites/default/files/2025-04/duplicate-publication-published-article-cope-flowchart.pdf"
    Source.institutionalSource
    "Publication-ethics guidance distinguishing original work, secondary/redundant manifestations and duplicate publication; republication does not manufacture a new upstream research event."
    Source.publicAttribution

cochraneMultipleReports : Source.AttributedSource
cochraneMultipleReports =
  Source.mkNoDOISource
    "Cochrane"
    "Cochrane Handbook Chapter 5: Collecting data — collating multiple reports"
    "Cochrane Training / Handbook for Systematic Reviews of Interventions"
    "current handbook inspected 2026"
    "https://training.cochrane.org/handbook/current/chapter-05"
    Source.institutionalSource
    "Systematic-review rule that multiple reports of the same study are collated so the study, not each report, is the unit of interest; directly supports provenance-root rather than publication-count independence accounting."
    Source.publicAttribution

w3cProvPrimer : Source.AttributedSource
w3cProvPrimer =
  Source.mkNoDOISource
    "W3C Provenance Working Group"
    "PROV Model Primer"
    "W3C Recommendation companion / provenance model primer"
    "2013"
    "https://www.w3.org/TR/prov-primer/"
    Source.technicalStandardSource
    "Provenance vocabulary distinguishes derivation, revision and quotation relations between entities; used here as a conceptual source-lineage reference, not as proof that a particular derivation occurred."
    Source.publicAttribution

canonicalAttributionProvenanceSOTASources : List Source.AttributedSource
canonicalAttributionProvenanceSOTASources =
  oriResearchMisconductDefinition
  ∷ copePlagiarismFlowchart
  ∷ copeRedundantPublicationFlowchart
  ∷ cochraneMultipleReports
  ∷ w3cProvPrimer
  ∷ []

canonicalAttributionProvenanceSOTAAtlas : Source.AttributedSourceAtlas
canonicalAttributionProvenanceSOTAAtlas =
  Source.mkSourceAtlas
    "Kitzerow attribution/provenance surrounding SOTA"
    "DASHI.Biology.KitzerowAttributionProvenanceSOTAExact"
    canonicalAttributionProvenanceSOTASources
    "Vocabulary and evidence-handling guidance for plagiarism/reuse, duplicate manifestations, independent evidence units and derivation provenance. External institutions own their guidance; DASHI owns only the typed cross-domain composition."

record AttributionProvenanceSOTABoundary : Set where
  constructor attributionProvenanceSOTABoundary
  field
    oriVocabularyIncludesIdeasProcessesResultsWords : Bool
    oriVocabularyIncludesIdeasProcessesResultsWordsIsTrue :
      oriVocabularyIncludesIdeasProcessesResultsWords ≡ true
    cochraneSeparatesReportsFromStudyUnits : Bool
    cochraneSeparatesReportsFromStudyUnitsIsTrue :
      cochraneSeparatesReportsFromStudyUnits ≡ true
    w3cSeparatesDerivationRevisionQuotationRelations : Bool
    w3cSeparatesDerivationRevisionQuotationRelationsIsTrue :
      w3cSeparatesDerivationRevisionQuotationRelations ≡ true
    copeTreatsDocumentaryEvidenceAsInvestigationInput : Bool
    copeTreatsDocumentaryEvidenceAsInvestigationInputIsTrue :
      copeTreatsDocumentaryEvidenceAsInvestigationInput ≡ true
    guidanceAutomaticallyAdjudicatesKitzerowClaim : Bool
    guidanceAutomaticallyAdjudicatesKitzerowClaimIsFalse :
      guidanceAutomaticallyAdjudicatesKitzerowClaim ≡ false
    institutionalGuidanceCreatesLegalConclusion : Bool
    institutionalGuidanceCreatesLegalConclusionIsFalse :
      institutionalGuidanceCreatesLegalConclusion ≡ false

open AttributionProvenanceSOTABoundary public

canonicalAttributionProvenanceSOTABoundary : AttributionProvenanceSOTABoundary
canonicalAttributionProvenanceSOTABoundary =
  attributionProvenanceSOTABoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
