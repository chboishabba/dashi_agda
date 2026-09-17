module DASHI.Education.DigitalESDDatabaseTranslatedQueriesExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDDatabaseSearchProtocolExact as Protocol
import DASHI.Education.DigitalESDDatabaseTranslationSyntaxExact as Syntax
import DASHI.Education.DigitalESDStructuredSearchExact as Search

record TranslatedQueryReceipt : Set where
  constructor translated-query-receipt
  field
    surface : Search.SearchSurface
    family : Search.SearchQueryFamily
    protocolQueryId : String
    syntaxReceipt : Syntax.DatabaseSyntaxReceipt
    exactTranslatedQuery : String
    executionObserved : Bool
    executionObservedIsFalse : executionObserved ≡ false
    translationBoundary : String

open TranslatedQueryReceipt public

------------------------------------------------------------------------
-- Scopus: TITLE-ABS-KEY over title / abstract / keywords.
------------------------------------------------------------------------

scopusQ1DigitalEducationESD : TranslatedQueryReceipt
scopusQ1DigitalEducationESD = translated-query-receipt Search.scopus Search.digitalEducationESD
  (Protocol.PlannedQuery.queryId Protocol.q1DigitalEducationESD) Syntax.scopusSyntaxReceipt
  "TITLE-ABS-KEY(((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (\"education for sustainable development\" OR ESD OR \"sustainable development education\" OR \"sustainability education\" OR \"environmental education\" OR \"sustainable education\")))"
  false refl
  "exact translation of protocol Q1 into Scopus TITLE-ABS-KEY; no execution/result receipt"

scopusQ2Transformation : TranslatedQueryReceipt
scopusQ2Transformation = translated-query-receipt Search.scopus Search.digitalEducationESD
  (Protocol.PlannedQuery.queryId Protocol.q2Transformation) Syntax.scopusSyntaxReceipt
  "TITLE-ABS-KEY(((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (\"education for sustainable development\" OR ESD OR \"sustainable development education\" OR \"sustainability education\" OR \"environmental education\" OR \"sustainable education\") AND (transform* OR \"system change\" OR institutional* OR \"institutional change\" OR \"whole institution\" OR curriculum OR pedagogy OR competenc* OR \"learning environment*\")))"
  false refl
  "exact translation of protocol Q2; transformation refinement remains in the digitalEducationESD family"

scopusQ3ReflexiveSustainability : TranslatedQueryReceipt
scopusQ3ReflexiveSustainability = translated-query-receipt Search.scopus Search.reflexiveDigitalSustainability
  (Protocol.PlannedQuery.queryId Protocol.q3ReflexiveSustainability) Syntax.scopusSyntaxReceipt
  "TITLE-ABS-KEY(((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (\"life cycle assessment\" OR LCA OR energy OR electricity OR carbon OR emission* OR water OR \"e-waste\" OR circular* OR repair* OR reuse OR recycl* OR upgrade* OR durability OR \"service life\")))"
  false refl
  "exact translation of protocol Q3 into Scopus"

scopusQ4LifecycleCircularity : TranslatedQueryReceipt
scopusQ4LifecycleCircularity = translated-query-receipt Search.scopus Search.lifecycleCircularity
  (Protocol.PlannedQuery.queryId Protocol.q4LifecycleCircularity) Syntax.scopusSyntaxReceipt
  "TITLE-ABS-KEY((\"life cycle assessment\" OR LCA OR energy OR electricity OR carbon OR emission* OR water OR \"e-waste\" OR circular* OR repair* OR reuse OR recycl* OR upgrade* OR durability OR \"service life\"))"
  false refl
  "explicit lifecycleCircularity family witness; intentionally broader than Q3 because it does not require an A-block digital-education term"

scopusQ5ParticipantGovernance : TranslatedQueryReceipt
scopusQ5ParticipantGovernance = translated-query-receipt Search.scopus Search.participantAgencyGovernance
  (Protocol.PlannedQuery.queryId Protocol.q5ParticipantGovernance) Syntax.scopusSyntaxReceipt
  "TITLE-ABS-KEY(((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (\"education for sustainable development\" OR ESD OR \"sustainable development education\" OR \"sustainability education\" OR \"environmental education\" OR \"sustainable education\") AND (\"student voice\" OR \"learner voice\" OR \"learner agency\" OR \"student agency\" OR participatory OR \"participatory research\" OR co-design OR codesign OR governance OR \"public accountability\")))"
  false refl
  "exact translation of protocol Q5 into Scopus"

scopusQ6LongitudinalInstitutional : TranslatedQueryReceipt
scopusQ6LongitudinalInstitutional = translated-query-receipt Search.scopus Search.longitudinalInstitutionalImpact
  (Protocol.PlannedQuery.queryId Protocol.q6LongitudinalInstitutional) Syntax.scopusSyntaxReceipt
  "TITLE-ABS-KEY(((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (\"education for sustainable development\" OR ESD OR \"sustainable development education\" OR \"sustainability education\" OR \"environmental education\" OR \"sustainable education\") AND (longitudinal OR long-term OR durability OR sustainab* OR institutionalisation OR institutionalization OR persistence OR retention OR follow-up OR \"follow up\")))"
  false refl
  "exact translation of protocol Q6 into Scopus"

scopusQ7OpenInteroperableRepairable : TranslatedQueryReceipt
scopusQ7OpenInteroperableRepairable = translated-query-receipt Search.scopus Search.openInteroperabilityRepairability
  (Protocol.PlannedQuery.queryId Protocol.q7OpenInteroperableRepairable) Syntax.scopusSyntaxReceipt
  "TITLE-ABS-KEY(((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (interoperab* OR \"open standard*\" OR \"open source\" OR OER OR \"open educational resource*\" OR portability OR migration OR export* OR \"vendor lock-in\" OR repairab* OR \"right to repair\")))"
  false refl
  "exact translation of protocol Q7 into Scopus"

------------------------------------------------------------------------
-- Web of Science Core Collection: TS Topic.
------------------------------------------------------------------------

wosQ1DigitalEducationESD : TranslatedQueryReceipt
wosQ1DigitalEducationESD = translated-query-receipt Search.webOfScience Search.digitalEducationESD
  (Protocol.PlannedQuery.queryId Protocol.q1DigitalEducationESD) Syntax.webOfScienceSyntaxReceipt
  "TS=((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (\"education for sustainable development\" OR ESD OR \"sustainable development education\" OR \"sustainability education\" OR \"environmental education\" OR \"sustainable education\"))"
  false refl
  "exact translation of protocol Q1 into Web of Science Core Collection TS Topic"

wosQ2Transformation : TranslatedQueryReceipt
wosQ2Transformation = translated-query-receipt Search.webOfScience Search.digitalEducationESD
  (Protocol.PlannedQuery.queryId Protocol.q2Transformation) Syntax.webOfScienceSyntaxReceipt
  "TS=((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (\"education for sustainable development\" OR ESD OR \"sustainable development education\" OR \"sustainability education\" OR \"environmental education\" OR \"sustainable education\") AND (transform* OR \"system change\" OR institutional* OR \"institutional change\" OR \"whole institution\" OR curriculum OR pedagogy OR competenc* OR \"learning environment*\"))"
  false refl
  "exact translation of protocol Q2 into Web of Science Core Collection TS Topic"

wosQ3ReflexiveSustainability : TranslatedQueryReceipt
wosQ3ReflexiveSustainability = translated-query-receipt Search.webOfScience Search.reflexiveDigitalSustainability
  (Protocol.PlannedQuery.queryId Protocol.q3ReflexiveSustainability) Syntax.webOfScienceSyntaxReceipt
  "TS=((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (\"life cycle assessment\" OR LCA OR energy OR electricity OR carbon OR emission* OR water OR \"e-waste\" OR circular* OR repair* OR reuse OR recycl* OR upgrade* OR durability OR \"service life\"))"
  false refl
  "exact translation of protocol Q3 into Web of Science Core Collection TS Topic"

wosQ4LifecycleCircularity : TranslatedQueryReceipt
wosQ4LifecycleCircularity = translated-query-receipt Search.webOfScience Search.lifecycleCircularity
  (Protocol.PlannedQuery.queryId Protocol.q4LifecycleCircularity) Syntax.webOfScienceSyntaxReceipt
  "TS=(\"life cycle assessment\" OR LCA OR energy OR electricity OR carbon OR emission* OR water OR \"e-waste\" OR circular* OR repair* OR reuse OR recycl* OR upgrade* OR durability OR \"service life\")"
  false refl
  "explicit lifecycleCircularity family witness; intentionally broader than Q3 because it does not require an A-block digital-education term"

wosQ5ParticipantGovernance : TranslatedQueryReceipt
wosQ5ParticipantGovernance = translated-query-receipt Search.webOfScience Search.participantAgencyGovernance
  (Protocol.PlannedQuery.queryId Protocol.q5ParticipantGovernance) Syntax.webOfScienceSyntaxReceipt
  "TS=((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (\"education for sustainable development\" OR ESD OR \"sustainable development education\" OR \"sustainability education\" OR \"environmental education\" OR \"sustainable education\") AND (\"student voice\" OR \"learner voice\" OR \"learner agency\" OR \"student agency\" OR participatory OR \"participatory research\" OR co-design OR codesign OR governance OR \"public accountability\"))"
  false refl
  "exact translation of protocol Q5 into Web of Science Core Collection TS Topic"

wosQ6LongitudinalInstitutional : TranslatedQueryReceipt
wosQ6LongitudinalInstitutional = translated-query-receipt Search.webOfScience Search.longitudinalInstitutionalImpact
  (Protocol.PlannedQuery.queryId Protocol.q6LongitudinalInstitutional) Syntax.webOfScienceSyntaxReceipt
  "TS=((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (\"education for sustainable development\" OR ESD OR \"sustainable development education\" OR \"sustainability education\" OR \"environmental education\" OR \"sustainable education\") AND (longitudinal OR long-term OR durability OR sustainab* OR institutionalisation OR institutionalization OR persistence OR retention OR follow-up OR \"follow up\"))"
  false refl
  "exact translation of protocol Q6 into Web of Science Core Collection TS Topic"

wosQ7OpenInteroperableRepairable : TranslatedQueryReceipt
wosQ7OpenInteroperableRepairable = translated-query-receipt Search.webOfScience Search.openInteroperabilityRepairability
  (Protocol.PlannedQuery.queryId Protocol.q7OpenInteroperableRepairable) Syntax.webOfScienceSyntaxReceipt
  "TS=((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (interoperab* OR \"open standard*\" OR \"open source\" OR OER OR \"open educational resource*\" OR portability OR migration OR export* OR \"vendor lock-in\" OR repairab* OR \"right to repair\"))"
  false refl
  "exact translation of protocol Q7 into Web of Science Core Collection TS Topic"

------------------------------------------------------------------------
-- IEEE Xplore: Command Search over All Metadata.
------------------------------------------------------------------------

ieeeQ1DigitalEducationESD : TranslatedQueryReceipt
ieeeQ1DigitalEducationESD = translated-query-receipt Search.ieeeXplore Search.digitalEducationESD
  (Protocol.PlannedQuery.queryId Protocol.q1DigitalEducationESD) Syntax.ieeeSyntaxReceipt
  "\"All Metadata\":(((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (\"education for sustainable development\" OR ESD OR \"sustainable development education\" OR \"sustainability education\" OR \"environmental education\" OR \"sustainable education\")))"
  false refl
  "exact translation of protocol Q1 into IEEE Xplore Command Search All Metadata"

ieeeQ2Transformation : TranslatedQueryReceipt
ieeeQ2Transformation = translated-query-receipt Search.ieeeXplore Search.digitalEducationESD
  (Protocol.PlannedQuery.queryId Protocol.q2Transformation) Syntax.ieeeSyntaxReceipt
  "\"All Metadata\":(((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (\"education for sustainable development\" OR ESD OR \"sustainable development education\" OR \"sustainability education\" OR \"environmental education\" OR \"sustainable education\") AND (transform* OR \"system change\" OR institutional* OR \"institutional change\" OR \"whole institution\" OR curriculum OR pedagogy OR competenc* OR \"learning environment*\")))"
  false refl
  "exact translation of protocol Q2 into IEEE Xplore Command Search All Metadata"

ieeeQ3ReflexiveSustainability : TranslatedQueryReceipt
ieeeQ3ReflexiveSustainability = translated-query-receipt Search.ieeeXplore Search.reflexiveDigitalSustainability
  (Protocol.PlannedQuery.queryId Protocol.q3ReflexiveSustainability) Syntax.ieeeSyntaxReceipt
  "\"All Metadata\":(((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (\"life cycle assessment\" OR LCA OR energy OR electricity OR carbon OR emission* OR water OR \"e-waste\" OR circular* OR repair* OR reuse OR recycl* OR upgrade* OR durability OR \"service life\")))"
  false refl
  "exact translation of protocol Q3 into IEEE Xplore Command Search All Metadata"

ieeeQ4LifecycleCircularity : TranslatedQueryReceipt
ieeeQ4LifecycleCircularity = translated-query-receipt Search.ieeeXplore Search.lifecycleCircularity
  (Protocol.PlannedQuery.queryId Protocol.q4LifecycleCircularity) Syntax.ieeeSyntaxReceipt
  "\"All Metadata\":((\"life cycle assessment\" OR LCA OR energy OR electricity OR carbon OR emission* OR water OR \"e-waste\" OR circular* OR repair* OR reuse OR recycl* OR upgrade* OR durability OR \"service life\"))"
  false refl
  "exact translation of protocol Q4 into IEEE Xplore Command Search All Metadata"

ieeeQ5ParticipantGovernance : TranslatedQueryReceipt
ieeeQ5ParticipantGovernance = translated-query-receipt Search.ieeeXplore Search.participantAgencyGovernance
  (Protocol.PlannedQuery.queryId Protocol.q5ParticipantGovernance) Syntax.ieeeSyntaxReceipt
  "\"All Metadata\":(((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (\"education for sustainable development\" OR ESD OR \"sustainable development education\" OR \"sustainability education\" OR \"environmental education\" OR \"sustainable education\") AND (\"student voice\" OR \"learner voice\" OR \"learner agency\" OR \"student agency\" OR participatory OR \"participatory research\" OR co-design OR codesign OR governance OR \"public accountability\")))"
  false refl
  "exact translation of protocol Q5 into IEEE Xplore Command Search All Metadata"

ieeeQ6LongitudinalInstitutional : TranslatedQueryReceipt
ieeeQ6LongitudinalInstitutional = translated-query-receipt Search.ieeeXplore Search.longitudinalInstitutionalImpact
  (Protocol.PlannedQuery.queryId Protocol.q6LongitudinalInstitutional) Syntax.ieeeSyntaxReceipt
  "\"All Metadata\":(((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (\"education for sustainable development\" OR ESD OR \"sustainable development education\" OR \"sustainability education\" OR \"environmental education\" OR \"sustainable education\") AND (longitudinal OR long-term OR durability OR sustainab* OR institutionalisation OR institutionalization OR persistence OR retention OR follow-up OR \"follow up\")))"
  false refl
  "exact translation of protocol Q6 into IEEE Xplore Command Search All Metadata"

ieeeQ7OpenInteroperableRepairable : TranslatedQueryReceipt
ieeeQ7OpenInteroperableRepairable = translated-query-receipt Search.ieeeXplore Search.openInteroperabilityRepairability
  (Protocol.PlannedQuery.queryId Protocol.q7OpenInteroperableRepairable) Syntax.ieeeSyntaxReceipt
  "\"All Metadata\":(((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (interoperab* OR \"open standard*\" OR \"open source\" OR OER OR \"open educational resource*\" OR portability OR migration OR export* OR \"vendor lock-in\" OR repairab* OR \"right to repair\")))"
  false refl
  "exact translation of protocol Q7 into IEEE Xplore Command Search All Metadata"

------------------------------------------------------------------------
-- ERIC: Solr-style API GET Search.
------------------------------------------------------------------------

ericQ1DigitalEducationESD : TranslatedQueryReceipt
ericQ1DigitalEducationESD = translated-query-receipt Search.eric Search.digitalEducationESD
  (Protocol.PlannedQuery.queryId Protocol.q1DigitalEducationESD) Syntax.ericSyntaxReceipt
  "((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (\"education for sustainable development\" OR ESD OR \"sustainable development education\" OR \"sustainability education\" OR \"environmental education\" OR \"sustainable education\"))"
  false refl
  "exact translation of protocol Q1 into ERIC API search syntax"

ericQ2Transformation : TranslatedQueryReceipt
ericQ2Transformation = translated-query-receipt Search.eric Search.digitalEducationESD
  (Protocol.PlannedQuery.queryId Protocol.q2Transformation) Syntax.ericSyntaxReceipt
  "((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (\"education for sustainable development\" OR ESD OR \"sustainable development education\" OR \"sustainability education\" OR \"environmental education\" OR \"sustainable education\") AND (transform* OR \"system change\" OR institutional* OR \"institutional change\" OR \"whole institution\" OR curriculum OR pedagogy OR competenc* OR \"learning environment*\"))"
  false refl
  "exact translation of protocol Q2 into ERIC API search syntax"

ericQ3ReflexiveSustainability : TranslatedQueryReceipt
ericQ3ReflexiveSustainability = translated-query-receipt Search.eric Search.reflexiveDigitalSustainability
  (Protocol.PlannedQuery.queryId Protocol.q3ReflexiveSustainability) Syntax.ericSyntaxReceipt
  "((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (\"life cycle assessment\" OR LCA OR energy OR electricity OR carbon OR emission* OR water OR \"e-waste\" OR circular* OR repair* OR reuse OR recycl* OR upgrade* OR durability OR \"service life\"))"
  false refl
  "exact translation of protocol Q3 into ERIC API search syntax"

ericQ4LifecycleCircularity : TranslatedQueryReceipt
ericQ4LifecycleCircularity = translated-query-receipt Search.eric Search.lifecycleCircularity
  (Protocol.PlannedQuery.queryId Protocol.q4LifecycleCircularity) Syntax.ericSyntaxReceipt
  "(\"life cycle assessment\" OR LCA OR energy OR electricity OR carbon OR emission* OR water OR \"e-waste\" OR circular* OR repair* OR reuse OR recycl* OR upgrade* OR durability OR \"service life\")"
  false refl
  "exact translation of protocol Q4 into ERIC API search syntax"

ericQ5ParticipantGovernance : TranslatedQueryReceipt
ericQ5ParticipantGovernance = translated-query-receipt Search.eric Search.participantAgencyGovernance
  (Protocol.PlannedQuery.queryId Protocol.q5ParticipantGovernance) Syntax.ericSyntaxReceipt
  "((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (\"education for sustainable development\" OR ESD OR \"sustainable development education\" OR \"sustainability education\" OR \"environmental education\" OR \"sustainable education\") AND (\"student voice\" OR \"learner voice\" OR \"learner agency\" OR \"student agency\" OR participatory OR \"participatory research\" OR co-design OR codesign OR governance OR \"public accountability\"))"
  false refl
  "exact translation of protocol Q5 into ERIC API search syntax"

ericQ6LongitudinalInstitutional : TranslatedQueryReceipt
ericQ6LongitudinalInstitutional = translated-query-receipt Search.eric Search.longitudinalInstitutionalImpact
  (Protocol.PlannedQuery.queryId Protocol.q6LongitudinalInstitutional) Syntax.ericSyntaxReceipt
  "((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (\"education for sustainable development\" OR ESD OR \"sustainable development education\" OR \"sustainability education\" OR \"environmental education\" OR \"sustainable education\") AND (longitudinal OR long-term OR durability OR sustainab* OR institutionalisation OR institutionalization OR persistence OR retention OR follow-up OR \"follow up\"))"
  false refl
  "exact translation of protocol Q6 into ERIC API search syntax"

ericQ7OpenInteroperableRepairable : TranslatedQueryReceipt
ericQ7OpenInteroperableRepairable = translated-query-receipt Search.eric Search.openInteroperabilityRepairability
  (Protocol.PlannedQuery.queryId Protocol.q7OpenInteroperableRepairable) Syntax.ericSyntaxReceipt
  "((\"digital education\" OR \"digital learning\" OR \"educational technology\" OR edtech OR \"online learning\" OR \"blended learning\" OR \"digital learning platform*\" OR \"generative AI\" OR GenAI OR \"artificial intelligence\") AND (interoperab* OR \"open standard*\" OR \"open source\" OR OER OR \"open educational resource*\" OR portability OR migration OR export* OR \"vendor lock-in\" OR repairab* OR \"right to repair\"))"
  false refl
  "exact translation of protocol Q7 into ERIC API search syntax"

canonicalTranslatedQueries : List TranslatedQueryReceipt
canonicalTranslatedQueries =
  scopusQ1DigitalEducationESD
  ∷ scopusQ2Transformation
  ∷ scopusQ3ReflexiveSustainability
  ∷ scopusQ4LifecycleCircularity
  ∷ scopusQ5ParticipantGovernance
  ∷ scopusQ6LongitudinalInstitutional
  ∷ scopusQ7OpenInteroperableRepairable
  ∷ wosQ1DigitalEducationESD
  ∷ wosQ2Transformation
  ∷ wosQ3ReflexiveSustainability
  ∷ wosQ4LifecycleCircularity
  ∷ wosQ5ParticipantGovernance
  ∷ wosQ6LongitudinalInstitutional
  ∷ wosQ7OpenInteroperableRepairable
  ∷ ieeeQ1DigitalEducationESD
  ∷ ieeeQ2Transformation
  ∷ ieeeQ3ReflexiveSustainability
  ∷ ieeeQ4LifecycleCircularity
  ∷ ieeeQ5ParticipantGovernance
  ∷ ieeeQ6LongitudinalInstitutional
  ∷ ieeeQ7OpenInteroperableRepairable
  ∷ ericQ1DigitalEducationESD
  ∷ ericQ2Transformation
  ∷ ericQ3ReflexiveSustainability
  ∷ ericQ4LifecycleCircularity
  ∷ ericQ5ParticipantGovernance
  ∷ ericQ6LongitudinalInstitutional
  ∷ ericQ7OpenInteroperableRepairable
  ∷ []

translatedQueryCount : Nat
translatedQueryCount = 28

data TranslatedQueryCreatesResultSet : Set where
data TranslatedQueryCreatesExecutionTimestamp : Set where
data TranslatedQueryCreatesSearchCompleteness : Set where

translatedQueryDoesNotCreateResultSet : TranslatedQueryCreatesResultSet → ⊥
translatedQueryDoesNotCreateResultSet ()

translatedQueryDoesNotCreateExecutionTimestamp : TranslatedQueryCreatesExecutionTimestamp → ⊥
translatedQueryDoesNotCreateExecutionTimestamp ()

translatedQueryDoesNotCreateSearchCompleteness : TranslatedQueryCreatesSearchCompleteness → ⊥
translatedQueryDoesNotCreateSearchCompleteness ()

record DatabaseTranslatedQueryBoundary : Set where
  constructor database-translated-query-boundary
  field
    scopusSevenExactQueriesFrozen : Bool
    scopusSevenExactQueriesFrozenIsTrue : scopusSevenExactQueriesFrozen ≡ true
    webOfScienceSevenExactQueriesFrozen : Bool
    webOfScienceSevenExactQueriesFrozenIsTrue : webOfScienceSevenExactQueriesFrozen ≡ true
    ieeeSevenExactQueriesFrozen : Bool
    ieeeSevenExactQueriesFrozenIsTrue : ieeeSevenExactQueriesFrozen ≡ true
    ericSevenExactQueriesFrozen : Bool
    ericSevenExactQueriesFrozenIsTrue : ericSevenExactQueriesFrozen ≡ true
    acmSevenExactQueriesFrozen : Bool
    acmSevenExactQueriesFrozenIsFalse : acmSevenExactQueriesFrozen ≡ false
    anyTranslatedQueryExecutionObserved : Bool
    anyTranslatedQueryExecutionObservedIsFalse : anyTranslatedQueryExecutionObserved ≡ false

open DatabaseTranslatedQueryBoundary public

canonicalDatabaseTranslatedQueryBoundary : DatabaseTranslatedQueryBoundary
canonicalDatabaseTranslatedQueryBoundary = database-translated-query-boundary
  true refl
  true refl
  true refl
  true refl
  false refl
  false refl

translatedQueryReading : String
translatedQueryReading =
  "Twenty-eight exact platform-specific queries are frozen across four databases (seven each for Scopus TITLE-ABS-KEY, Web of Science Core Collection TS Topic, IEEE Xplore Command Search, and ERIC API search). ACM DL exact queries remain explicit translation debt (7 of 35 planned queries unpaid). No translated query has been executed, counted, exported, deduplicated, screened or promoted into evidence completeness."
