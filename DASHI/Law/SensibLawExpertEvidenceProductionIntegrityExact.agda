module DASHI.Law.SensibLawExpertEvidenceProductionIntegrityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- GENERIC EXPERT-EVIDENCE PRODUCTION INTEGRITY
--
-- An expert report is a production process, not a truth primitive:
--
--   source data -> selected/observed data -> inference -> opinion -> report use
--
-- This owner deliberately stops before any Australian family-law adapter.
-- It provides reusable carriers, query-indexed adequacy, abstention, and
-- authority firewalls.  It does not decide admissibility, negligence,
-- professional misconduct, legal breach, or truth of any expert conclusion.
------------------------------------------------------------------------

record ExpertData : Set where
  constructor expertData
  field
    dataReference : String
    provenanceReference : String

record ExpertInference : Set where
  constructor expertInference
  field
    inferenceReference : String
    methodReference : String
    consumedEvidenceReferences : List String
    excludedEvidenceReferences : List String
    assumptionReferences : List String
    limitationReferences : List String

record ExpertOpinion : Set where
  constructor expertOpinion
  field
    opinionReference : String
    inferenceReference : String
    opinionText : String

record ExpertReport : Set where
  constructor expertReport
  field
    reportReference : String
    opinionReferences : List String
    productionReference : String

record ExpertProduction : Set where
  constructor expertProduction
  field
    availableSourceReferences : List String
    acquiredSourceReferences : List String
    excludedSourceReferences : List String
    observationConditionReferences : List String
    methodReferences : List String
    assumptionReferences : List String
    inferenceReferences : List String
    opinionReferences : List String
    reportReference : String

------------------------------------------------------------------------
-- Abstention is a valid output when the declared evidence surface is
-- insufficient for a responsible opinion.
------------------------------------------------------------------------

data OpinionDisposition : Set where
  supportedOpinion : OpinionDisposition
  conditionalOpinion : OpinionDisposition
  abstainedInsufficientEvidence : OpinionDisposition

------------------------------------------------------------------------
-- Exact finite observer-adequacy witness.
--
-- Two possible worlds project to the same acquired expert surface because a
-- risk source was not observed.  The descriptive query is constant, but the
-- risk query differs.  Therefore the risk answer cannot factor through that
-- erased-source observation surface.
------------------------------------------------------------------------

data RiskWorld : Set where
  noRelevantRiskSource : RiskWorld
  relevantRiskSourceExists : RiskWorld

data AcquiredExpertSurface : Set where
  sameAcquiredSurface : AcquiredExpertSurface

data ExpertConsumerQuery : Set where
  descriptiveQuery : ExpertConsumerQuery
  riskQuery : ExpertConsumerQuery

data ExpertConsumerAnswer : Set where
  sameDescription : ExpertConsumerAnswer
  lowerRiskAnswer : ExpertConsumerAnswer
  higherRiskAnswer : ExpertConsumerAnswer

acquiredExpertSurface : RiskWorld → AcquiredExpertSurface
acquiredExpertSurface world = sameAcquiredSurface

expertConsumerAnswer : ExpertConsumerQuery → RiskWorld → ExpertConsumerAnswer
expertConsumerAnswer descriptiveQuery world = sameDescription
expertConsumerAnswer riskQuery noRelevantRiskSource = lowerRiskAnswer
expertConsumerAnswer riskQuery relevantRiskSourceExists = higherRiskAnswer

expertConsumerSemantics :
  Query.QuerySemantics RiskWorld ExpertConsumerQuery ExpertConsumerAnswer
expertConsumerSemantics = Query.querySemantics expertConsumerAnswer

descriptiveQueryAdequate :
  Query.AdequateFor acquiredExpertSurface expertConsumerSemantics descriptiveQuery
descriptiveQueryAdequate =
  Query.factorsForQuery
    (λ surface → sameDescription)
    (λ world → refl)

RiskQueryAdequacyDefect : Set₁
RiskQueryAdequacyDefect =
  Query.QueryAdequacyDefect acquiredExpertSurface expertConsumerSemantics riskQuery

riskQueryAdequacyDefect : RiskQueryAdequacyDefect
riskQueryAdequacyDefect =
  Query.queryAdequacyDefect
    noRelevantRiskSource
    relevantRiskSourceExists
    refl
    (λ ())

RiskQueryAdequate : Set₁
RiskQueryAdequate =
  Query.AdequateFor acquiredExpertSurface expertConsumerSemantics riskQuery

riskQueryNotAdequate : RiskQueryAdequate → ⊥
riskQueryNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation riskQueryAdequacyDefect

------------------------------------------------------------------------
-- SOURCE-GENEALOGY / INDEPENDENCE CROSS-POLLINATION
--
-- Reuses the same non-factorability grammar already exercised by the repo's
-- testimony / replication / source-dependency lanes: two visible reports can
-- agree while arising from independent paths or one common source.  Report
-- multiplicity and agreement therefore cannot manufacture provenance
-- independence.  The canonical repair is to retain the visible report surface
-- and join the missing genealogy coordinate explicitly.
------------------------------------------------------------------------

data ExpertReportPairWorld : Set where
  agreeingIndependentReports : ExpertReportPairWorld
  agreeingCommonSourceReports : ExpertReportPairWorld

data ReportAgreementSurface : Set where
  sameObservedReportAgreement : ReportAgreementSurface

data ReportSourceGenealogy : Set where
  independentReportPaths : ReportSourceGenealogy
  commonSourceReportPath : ReportSourceGenealogy

data SourceGenealogyQuery : Set where
  reportAgreementQuery : SourceGenealogyQuery
  sourceIndependenceQuery : SourceGenealogyQuery

data SourceGenealogyAnswer : Set where
  sameAgreementAnswer : SourceGenealogyAnswer
  independentSourceAnswer : SourceGenealogyAnswer
  commonSourceAnswer : SourceGenealogyAnswer

reportAgreementSurface : ExpertReportPairWorld → ReportAgreementSurface
reportAgreementSurface world = sameObservedReportAgreement

reportSourceGenealogy : ExpertReportPairWorld → ReportSourceGenealogy
reportSourceGenealogy agreeingIndependentReports = independentReportPaths
reportSourceGenealogy agreeingCommonSourceReports = commonSourceReportPath

sourceGenealogyAnswer :
  SourceGenealogyQuery → ExpertReportPairWorld → SourceGenealogyAnswer
sourceGenealogyAnswer reportAgreementQuery world = sameAgreementAnswer
sourceGenealogyAnswer sourceIndependenceQuery agreeingIndependentReports =
  independentSourceAnswer
sourceGenealogyAnswer sourceIndependenceQuery agreeingCommonSourceReports =
  commonSourceAnswer

sourceGenealogySemantics :
  Query.QuerySemantics
    ExpertReportPairWorld SourceGenealogyQuery SourceGenealogyAnswer
sourceGenealogySemantics = Query.querySemantics sourceGenealogyAnswer

reportAgreementQueryAdequate :
  Query.AdequateFor
    reportAgreementSurface sourceGenealogySemantics reportAgreementQuery
reportAgreementQueryAdequate =
  Query.factorsForQuery
    (λ surface → sameAgreementAnswer)
    (λ world → refl)

SourceIndependenceQueryAdequacyDefect : Set₁
SourceIndependenceQueryAdequacyDefect =
  Query.QueryAdequacyDefect
    reportAgreementSurface sourceGenealogySemantics sourceIndependenceQuery

sourceIndependenceQueryAdequacyDefect :
  SourceIndependenceQueryAdequacyDefect
sourceIndependenceQueryAdequacyDefect =
  Query.queryAdequacyDefect
    agreeingIndependentReports
    agreeingCommonSourceReports
    refl
    (λ ())

SourceIndependenceQueryAdequate : Set₁
SourceIndependenceQueryAdequate =
  Query.AdequateFor
    reportAgreementSurface sourceGenealogySemantics sourceIndependenceQuery

sourceIndependenceQueryNotAdequate :
  SourceIndependenceQueryAdequate → ⊥
sourceIndependenceQueryNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation
    sourceIndependenceQueryAdequacyDefect

reportAgreementPlusGenealogy :
  ExpertReportPairWorld → ReportAgreementSurface × ReportSourceGenealogy
reportAgreementPlusGenealogy =
  Observer.pairObserver reportAgreementSurface reportSourceGenealogy

reportAgreementPlusGenealogyRefinesAgreement :
  Observer.Refines reportAgreementSurface reportAgreementPlusGenealogy
reportAgreementPlusGenealogyRefinesAgreement =
  Observer.pairRefinesLeft reportAgreementSurface reportSourceGenealogy

reportAgreementPlusGenealogyStrictRefinement :
  Observer.StrictRefinement reportAgreementSurface reportAgreementPlusGenealogy
reportAgreementPlusGenealogyStrictRefinement =
  Observer.strictPairRefinement
    reportAgreementSurface
    reportSourceGenealogy
    agreeingIndependentReports
    agreeingCommonSourceReports
    refl
    (λ ())

data MultipleReportsAutomaticallyIndependent : Set where
data AgreementAutomaticallyIndependentCorroboration : Set where
data DependenceMeansNoEvidence : Set where

multipleReportsDoNotAutomaticallyCreateIndependence :
  MultipleReportsAutomaticallyIndependent → ⊥
multipleReportsDoNotAutomaticallyCreateIndependence ()

agreementDoesNotAutomaticallyCreateIndependentCorroboration :
  AgreementAutomaticallyIndependentCorroboration → ⊥
agreementDoesNotAutomaticallyCreateIndependentCorroboration ()

dependenceDoesNotMeanNoEvidence : DependenceMeansNoEvidence → ⊥
dependenceDoesNotMeanNoEvidence ()

------------------------------------------------------------------------
-- Closed authority bundle.
--
-- Expert status, report production, an adequacy witness, or a defect witness
-- does not by itself grant truth, admissibility, clinical, empirical, legal,
-- or any other authority represented by AuthorityNonPromotionCore.
------------------------------------------------------------------------

expertProductionAuthorityBoundary : Authority.AuthorityNonPromotionBundle
expertProductionAuthorityBoundary =
  Authority.mkClosedAuthorityNonPromotionBundle
    "SensibLaw expert-evidence production integrity is structurally typed but non-promoting"

expertProductionPromotesAnyAuthority : Bool
expertProductionPromotesAnyAuthority =
  Authority.promotesAnyAuthority expertProductionAuthorityBoundary

expertProductionPromotesAnyAuthorityIsFalse :
  expertProductionPromotesAnyAuthority ≡ false
expertProductionPromotesAnyAuthorityIsFalse =
  Authority.promotesAnyAuthorityIsFalse expertProductionAuthorityBoundary

------------------------------------------------------------------------
-- Core WrongType / promotion boundary.
------------------------------------------------------------------------

record ExpertProductionBoundary : Set where
  constructor expertProductionBoundary
  field
    dataInferenceOpinionCollapsed : Bool
    expertStatusAutomaticallyTruthAuthority : Bool
    reportAdmissionRepairsUpstreamIntegrity : Bool
    crossExaminationRetroactivelyAddsUnobservedInput : Bool
    disputedRiskAutomaticallyIrrelevant : Bool
    oneQueryAdequacyImpliesAllQueryAdequacy : Bool
    observerDefectAutomaticallyMakesOpinionFalse : Bool
    professionalQualificationAutomaticallyForensicCompliance : Bool
    insufficientEvidenceMayRequireAbstention : Bool
    queryIndexedAdequacyRequired : Bool

open ExpertProductionBoundary public

canonicalExpertProductionBoundary : ExpertProductionBoundary
canonicalExpertProductionBoundary =
  expertProductionBoundary
    false
    false
    false
    false
    false
    false
    false
    false
    true
    true

------------------------------------------------------------------------
-- Empty bad-promotion propositions make the principal firewalls reusable by
-- downstream adapters without turning a Boolean boundary into legal doctrine.
------------------------------------------------------------------------

data ExpertStatusAutomaticallyTruth : Set where
data ReportAdmissionRepairsMissingInput : Set where
data CrossExaminationAddsUnobservedInput : Set where
data DisputedRiskIsIrrelevant : Set where
data ObserverDefectMakesOpinionFalse : Set where
data QualificationAutomaticallyForensicCompliance : Set where

expertStatusDoesNotAutomaticallyCreateTruth :
  ExpertStatusAutomaticallyTruth → ⊥
expertStatusDoesNotAutomaticallyCreateTruth ()

reportAdmissionDoesNotRepairMissingInput :
  ReportAdmissionRepairsMissingInput → ⊥
reportAdmissionDoesNotRepairMissingInput ()

crossExaminationDoesNotAddUnobservedInput :
  CrossExaminationAddsUnobservedInput → ⊥
crossExaminationDoesNotAddUnobservedInput ()

disputedRiskDoesNotBecomeIrrelevant :
  DisputedRiskIsIrrelevant → ⊥
disputedRiskDoesNotBecomeIrrelevant ()

observerDefectDoesNotProveOpinionFalse :
  ObserverDefectMakesOpinionFalse → ⊥
observerDefectDoesNotProveOpinionFalse ()

qualificationDoesNotAutomaticallyProveForensicCompliance :
  QualificationAutomaticallyForensicCompliance → ⊥
qualificationDoesNotAutomaticallyProveForensicCompliance ()
