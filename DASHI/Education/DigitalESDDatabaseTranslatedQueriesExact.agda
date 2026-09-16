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
  ∷ []

translatedQueryCount : Nat
translatedQueryCount = 14

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
    ieeeSevenExactQueriesFrozenIsFalse : ieeeSevenExactQueriesFrozen ≡ false
    ericSevenExactQueriesFrozen : Bool
    ericSevenExactQueriesFrozenIsFalse : ericSevenExactQueriesFrozen ≡ false
    acmSevenExactQueriesFrozen : Bool
    acmSevenExactQueriesFrozenIsFalse : acmSevenExactQueriesFrozen ≡ false
    anyTranslatedQueryExecutionObserved : Bool
    anyTranslatedQueryExecutionObservedIsFalse : anyTranslatedQueryExecutionObserved ≡ false

open DatabaseTranslatedQueryBoundary public

canonicalDatabaseTranslatedQueryBoundary : DatabaseTranslatedQueryBoundary
canonicalDatabaseTranslatedQueryBoundary = database-translated-query-boundary
  true refl
  true refl
  false refl
  false refl
  false refl
  false refl

translatedQueryReading : String
translatedQueryReading =
  "Fourteen exact platform-specific queries are frozen: seven Scopus TITLE-ABS-KEY translations and seven Web of Science Core Collection TS Topic translations of the seven-query protocol. IEEE Xplore, ERIC and ACM DL exact query sets remain explicit translation debt. No translated query has been executed, counted, exported, deduplicated, screened or promoted into evidence completeness."
