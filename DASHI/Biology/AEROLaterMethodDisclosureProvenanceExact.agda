module DASHI.Biology.AEROLaterMethodDisclosureProvenanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LATER METHOD DISCLOSURE / TEMPORAL PROVENANCE
--
-- AERO's 2024 report, "The impact of context on evidence-based practices",
-- later publishes methodology/limitations for the context review summarised in
-- the 2022 article cited by the 2023 How students learn best overview.
--
-- Important attribution rule:
--   later disclosure can illuminate the method/history of an earlier evidence
--   surface, but it is not silently rewritten as a contemporaneous 2023
--   citation or as proof of what every 2023 reader could verify at that time.
------------------------------------------------------------------------

data TemporalSourceRole : Set where
  contemporaneousCitation
  laterMethodDisclosure
  laterCorrection
  laterReplication : TemporalSourceRole

record TemporalMethodReceipt : Set where
  constructor temporalMethodReceipt
  field
    sourceTitle : String
    publicationYear : Nat
    role : TemporalSourceRole
    earlierSurface : String
    methodReading : String
    limitationReading : String

open TemporalMethodReceipt public

contextReview2024 : TemporalMethodReceipt
contextReview2024 =
  temporalMethodReceipt
    "The impact of context on evidence-based practices: A rapid literature scan on formative assessment, explicit instruction and mastery learning"
    2024
    laterMethodDisclosure
    "Gonsalkorale 2022 context article / AERO 2023 How students learn best context claim"
    "AERO reports an umbrella-style review of meta-analyses for three practices, summarising overall effect sizes and contextual variables; relevant meta-analyses were identified through EEF Toolkit, Visible Learning MetaX and supplementary searches."
    "The report says the review was not exhaustive, did not review individual studies, excluded qualitative/narrative evidence, relied on meta-analysis authors for contextual variables, and sometimes required researcher judgement to harmonise contexts."

------------------------------------------------------------------------
-- The later report supports a more precise source-chain description.
------------------------------------------------------------------------

data ReviewDepth : Set where
  articleSummary
  metaAnalyticUmbrella
  individualStudyReview
  rawDataReanalysis : ReviewDepth

contextReviewDepth : ReviewDepth
contextReviewDepth = metaAnalyticUmbrella

metaUmbrella≢individualStudyReview :
  ¬ (metaAnalyticUmbrella ≡ individualStudyReview)
metaUmbrella≢individualStudyReview ()

metaUmbrella≢rawDataReanalysis :
  ¬ (metaAnalyticUmbrella ≡ rawDataReanalysis)
metaUmbrella≢rawDataReanalysis ()

------------------------------------------------------------------------
-- Explicit limitations become transport obligations rather than hidden prose.
------------------------------------------------------------------------

data MethodLimitation : Set where
  nonExhaustiveSearch
  noIndividualStudyReview
  qualitativeEvidenceExcluded
  contextVariablesSometimesSparse
  interventionSpecificityVariable
  outcomeMeasuresVariable
  researcherHarmonisationRequired
  limitedAustralianContextEvidence : MethodLimitation

contextReviewLimitations : List MethodLimitation
contextReviewLimitations =
  nonExhaustiveSearch
  ∷ noIndividualStudyReview
  ∷ qualitativeEvidenceExcluded
  ∷ contextVariablesSometimesSparse
  ∷ interventionSpecificityVariable
  ∷ outcomeMeasuresVariable
  ∷ researcherHarmonisationRequired
  ∷ limitedAustralianContextEvidence
  ∷ []

------------------------------------------------------------------------
-- Temporal non-promotion gates.
------------------------------------------------------------------------

data LaterDisclosureWasContemporaneousCitation : Set where

data LaterDisclosureProvesEarlierReaderAccess : Set where

data UmbrellaReviewProvesEveryIndividualStudy : Set where

data BroadContextSynthesisProvesUniversalTransport : Set where

laterDisclosureNotContemporaneousCitation :
  LaterDisclosureWasContemporaneousCitation → ⊥
laterDisclosureNotContemporaneousCitation ()

laterDisclosureDoesNotProveEarlierReaderAccess :
  LaterDisclosureProvesEarlierReaderAccess → ⊥
laterDisclosureDoesNotProveEarlierReaderAccess ()

umbrellaReviewDoesNotProveEveryIndividualStudy :
  UmbrellaReviewProvesEveryIndividualStudy → ⊥
umbrellaReviewDoesNotProveEveryIndividualStudy ()

broadContextSynthesisDoesNotProveUniversalTransport :
  BroadContextSynthesisProvesUniversalTransport → ⊥
broadContextSynthesisDoesNotProveUniversalTransport ()

record LaterMethodDisclosureBoundary : Set where
  constructor laterMethodDisclosureBoundary
  field
    laterMethodDisclosureUsefulForRetrospectiveAudit : Bool
    laterPublicationEqualsEarlierCitation : Bool
    metaAnalysisUmbrellaEqualsIndividualStudyAudit : Bool
    explicitLimitationsPropagateToTransportAudit : Bool
    methodDisclosureCreatesUniversalTransport : Bool

canonicalLaterMethodDisclosureBoundary : LaterMethodDisclosureBoundary
canonicalLaterMethodDisclosureBoundary =
  laterMethodDisclosureBoundary true false false true false
