module DASHI.Law.SensibLawLegalResearchProviderSourceAtlasExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- LEGAL RESEARCH PROVIDER / QUERY-SEMANTICS SOURCE ATTRIBUTION
--
-- Provider documentation owns syntax/capability claims only.  A successful
-- query/citation traversal is not a legal holding, proposition correspondence,
-- current-authority assessment, applicability finding, or proof payment.
------------------------------------------------------------------------

austliiUserGuide : Source.AttributedSource
austliiUserGuide =
  Source.mkNoDOISource
    "Australasian Legal Information Institute (AustLII)"
    "AustLII User Guide"
    "AustLII"
    "2024"
    "https://www.austlii.edu.au/austlii/guide/user_guide.pdf"
    Source.institutionalSource
    "primary provider documentation for Boolean/proximity search semantics including near, w/n, /n/, and pre/n; syntax support does not establish relevance or legal authority"
    Source.publicAttribution

sinoManual : Source.AttributedSource
sinoManual =
  Source.mkNoDOISource
    "Australasian Legal Information Institute (AustLII)"
    "Sino - A Text Search Engine: Manual"
    "AustLII Technical Library"
    "2024"
    "https://www.austlii.edu.au/techlib/software/sino/Manual.pdf"
    Source.technicalStandardSource
    "primary technical documentation for Sino proximity/search operators; lowering QueryExpr to Sino syntax remains retrieval compilation rather than semantic/legal proof"
    Source.publicAttribution

jadePlatform : Source.AttributedSource
jadePlatform =
  Source.mkNoDOISource
    "BarNet JADE"
    "JADE Professional legal research platform / Case Trace and citation features"
    "JADE"
    "2026"
    "https://professional.jade.io/"
    Source.practitionerSource
    "provider-owned description of citation checking, cases-citing/cited-by, legislation and Case Trace capabilities; provider traversal output requires separate proposition/treatment assessment"
    Source.publicAttribution

record LegalResearchProviderSourceBoundary : Set where
  constructor legal-research-provider-source-boundary
  field
    providerSyntaxCreatesLegalMeaning : Bool
    providerSyntaxCreatesLegalMeaningIsFalse : providerSyntaxCreatesLegalMeaning ≡ false
    citationTraversalCreatesTreatmentFinding : Bool
    citationTraversalCreatesTreatmentFindingIsFalse : citationTraversalCreatesTreatmentFinding ≡ false
    searchHitCreatesProofPayment : Bool
    searchHitCreatesProofPaymentIsFalse : searchHitCreatesProofPayment ≡ false
    providerDescriptionCreatesCoverageCompleteness : Bool
    providerDescriptionCreatesCoverageCompletenessIsFalse : providerDescriptionCreatesCoverageCompleteness ≡ false

canonicalLegalResearchProviderSourceBoundary : LegalResearchProviderSourceBoundary
canonicalLegalResearchProviderSourceBoundary =
  legal-research-provider-source-boundary false refl false refl false refl false refl
