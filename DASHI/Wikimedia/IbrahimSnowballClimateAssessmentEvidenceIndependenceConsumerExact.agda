module DASHI.Wikimedia.IbrahimSnowballClimateAssessmentEvidenceIndependenceConsumerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballMemoryRepetitionSourceDependencyConsensusBidiExact as Dependency
import DASHI.Wikimedia.IbrahimSnowballEvidenceSynthesisPeerReviewConflictIndependenceBidiExact as Synthesis
import DASHI.Wikimedia.IbrahimSnowballAtomicClaimIntentExperimentAdequacyBidiExact as Atomic
import DASHI.Wikimedia.SensibLawNatClimateReviewHandoffExact as NatClimate

------------------------------------------------------------------------
-- CONCRETE IBRAHIM CONSUMER STRESS TEST
--
-- climate assessment / evidence synthesis / source dependence
--              x
-- SensibLaw Wikidata climate statement-bundle review
--
-- The word "review" is deliberately not treated as one semantic atom.  A
-- Wikidata migration/reviewer packet, a peer review, a systematic review and an
-- IPCC assessment/synthesis report are different consumers even where they
-- concern the same broad climate topic.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim climate-assessment evidence-independence consumer"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create evidence independence, assessment adequacy, source authority, scientific consensus truth or Wikidata migration equivalence")

climateChangeQid : Identity.ExternalIdentityDemand
climateChangeQid = mkQid "climate change" "Q125928"

ipccAR6SynthesisReportQid : Identity.ExternalIdentityDemand
ipccAR6SynthesisReportQid = mkQid
  "IPCC 2023 AR6 Climate Change 2023 Synthesis Report"
  "Q140144650"

------------------------------------------------------------------------
-- Dewey is many-view navigation: one climate-change QID currently carries
-- several DDC coordinates.  Retain them all rather than selecting one as the
-- semantic parent.
------------------------------------------------------------------------

climateChangeDeweyEnvironment : Dewey.DeweyCoordinate
climateChangeDeweyEnvironment = Dewey.mkVerifiedDewey
  "climate change"
  "363.7"
  "Wikidata Q125928 DDC statement inspected 2026-09-11"

climateChangeDeweyClimatology : Dewey.DeweyCoordinate
climateChangeDeweyClimatology = Dewey.mkVerifiedDewey
  "climate change"
  "551.6"
  "Wikidata Q125928 DDC statement inspected 2026-09-11"

climateChangeDeweyEcology : Dewey.DeweyCoordinate
climateChangeDeweyEcology = Dewey.mkVerifiedDewey
  "climate change"
  "577.22"
  "Wikidata Q125928 DDC statement inspected 2026-09-11"

climateChangeDeweyAgriculture : Dewey.DeweyCoordinate
climateChangeDeweyAgriculture = Dewey.mkVerifiedDewey
  "climate change"
  "632.1"
  "Wikidata Q125928 DDC statement inspected 2026-09-11"

climateChangeDeweyHumanEcology : Dewey.DeweyCoordinate
climateChangeDeweyHumanEcology = Dewey.mkVerifiedDewey
  "climate change"
  "304.28"
  "Wikidata Q125928 DDC statement inspected 2026-09-11"

------------------------------------------------------------------------
-- Exact source object for the concrete scientific-assessment carrier.
------------------------------------------------------------------------

ipccAR6SynthesisReportSource : Attribution.AttributedSource
ipccAR6SynthesisReportSource = Attribution.mkDOISource
  "Intergovernmental Panel on Climate Change; Core Writing Team; Hoesung Lee; José Romero (eds.)"
  "Climate Change 2023: Synthesis Report. Contribution of Working Groups I, II and III to the Sixth Assessment Report of the Intergovernmental Panel on Climate Change"
  "IPCC, Geneva"
  "2023"
  "10.59327/IPCC/AR6-9789291691647"
  "https://doi.org/10.59327/IPCC/AR6-9789291691647"
  Attribution.institutionalSource
  "bounded assessment/synthesis-report identity; the report aggregates assessed evidence but report identity alone does not expose or pay every underlying source-dependency relation"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Existing generic grammar reused rather than forked.
------------------------------------------------------------------------

dependencyBoundary : Dependency.MemoryRepetitionSourceDependencyConsensusBoundary
dependencyBoundary = Dependency.canonicalMemoryRepetitionSourceDependencyConsensusBoundary

synthesisBoundary : Synthesis.EvidenceSynthesisPeerReviewIndependenceBoundary
synthesisBoundary = Synthesis.canonicalEvidenceSynthesisPeerReviewIndependenceBoundary

atomicBoundary : Atomic.AtomicClaimIntentExperimentAdequacyBoundary
atomicBoundary = Atomic.canonicalAtomicClaimIntentExperimentAdequacyBoundary

natClimateBoundary : NatClimate.NatClimateHandoffBoundary
natClimateBoundary = NatClimate.canonicalNatClimateHandoffBoundary

------------------------------------------------------------------------
-- Regression 1: "review" cannot factor review-consumer semantics.
------------------------------------------------------------------------

data ReviewCase : Set where
  sameReviewWordMigrationReview sameReviewWordScientificAssessment : ReviewCase

data ReviewWordSurface : Set where reviewLabel : ReviewWordSurface
data ReviewConsumer : Set where wikidataMigrationConsumer scientificAssessmentConsumer : ReviewConsumer

reviewWordSurface : ReviewCase → ReviewWordSurface
reviewWordSurface _ = reviewLabel

reviewConsumer : ReviewCase → ReviewConsumer
reviewConsumer sameReviewWordMigrationReview = wikidataMigrationConsumer
reviewConsumer sameReviewWordScientificAssessment = scientificAssessmentConsumer

reviewConsumerDefect : INF.NonFactorabilityWitness reviewWordSurface reviewConsumer
reviewConsumerDefect = INF.nonFactorabilityWitness
  sameReviewWordMigrationReview sameReviewWordScientificAssessment refl (λ ())

reviewLabelCannotFactorReviewConsumer :
  INF.FactorsThrough reviewWordSurface reviewConsumer → ⊥
reviewLabelCannotFactorReviewConsumer =
  INF.witnessRulesOutEveryFlatFactorisation reviewConsumerDefect

------------------------------------------------------------------------
-- Regression 2: one assessment/synthesis carrier cannot recover the dependency
-- genealogy of all evidence supporting a conclusion.
------------------------------------------------------------------------

data AssessmentCase : Set where
  sameAssessmentOutputIndependentLines sameAssessmentOutputOverlappingLines : AssessmentCase

data AssessmentSurface : Set where sameAssessmentConclusion : AssessmentSurface
data EvidenceGenealogy : Set where substantiallyIndependentLines materiallyOverlappingLines : EvidenceGenealogy

assessmentSurface : AssessmentCase → AssessmentSurface
assessmentSurface _ = sameAssessmentConclusion

evidenceGenealogy : AssessmentCase → EvidenceGenealogy
evidenceGenealogy sameAssessmentOutputIndependentLines = substantiallyIndependentLines
evidenceGenealogy sameAssessmentOutputOverlappingLines = materiallyOverlappingLines

assessmentDependencyDefect : INF.NonFactorabilityWitness assessmentSurface evidenceGenealogy
assessmentDependencyDefect = INF.nonFactorabilityWitness
  sameAssessmentOutputIndependentLines sameAssessmentOutputOverlappingLines refl (λ ())

assessmentConclusionCannotFactorEvidenceIndependence :
  INF.FactorsThrough assessmentSurface evidenceGenealogy → ⊥
assessmentConclusionCannotFactorEvidenceIndependence =
  INF.witnessRulesOutEveryFlatFactorisation assessmentDependencyDefect

------------------------------------------------------------------------
-- Regression 3: statement-bundle cleanliness cannot recover scientific
-- proposition adequacy.  This is the concrete SensibLaw x AtomicClaim weld.
------------------------------------------------------------------------

data StatementCase : Set where
  sameCleanShapeClaimAdequate sameCleanShapeClaimMisSpecified : StatementCase

data StatementShape : Set where sameCleanStatementBundle : StatementShape
data ScientificClaimAdequacy : Set where scientificClaimAdequate scientificClaimMisSpecified : ScientificClaimAdequacy

statementShape : StatementCase → StatementShape
statementShape _ = sameCleanStatementBundle

scientificClaimAdequacy : StatementCase → ScientificClaimAdequacy
scientificClaimAdequacy sameCleanShapeClaimAdequate = scientificClaimAdequate
scientificClaimAdequacy sameCleanShapeClaimMisSpecified = scientificClaimMisSpecified

statementAdequacyDefect : INF.NonFactorabilityWitness statementShape scientificClaimAdequacy
statementAdequacyDefect = INF.nonFactorabilityWitness
  sameCleanShapeClaimAdequate sameCleanShapeClaimMisSpecified refl (λ ())

cleanStatementShapeCannotFactorScientificClaimAdequacy :
  INF.FactorsThrough statementShape scientificClaimAdequacy → ⊥
cleanStatementShapeCannotFactorScientificClaimAdequacy =
  INF.witnessRulesOutEveryFlatFactorisation statementAdequacyDefect

------------------------------------------------------------------------
-- Reverse BIDI constraints.
------------------------------------------------------------------------

record ClimateAssessmentReverseConstraint : Set where
  constructor climate-assessment-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open ClimateAssessmentReverseConstraint public

climateConstraint : ClimateAssessmentReverseConstraint
climateConstraint = climate-assessment-reverse-constraint
  "Climate change / climate science"
  "physical claim, atomic proposition, evidence family, source genealogy, synthesis judgement, uncertainty language and policy/legal use remain distinct"
  false

assessmentConstraint : ClimateAssessmentReverseConstraint
assessmentConstraint = climate-assessment-reverse-constraint
  "Evidence synthesis / scientific assessment"
  "assessment-report identity, included studies, evidence dependence, methodological diversity, assessed conclusion and consensus remain distinct"
  false

wikimediaConstraint : ClimateAssessmentReverseConstraint
wikimediaConstraint = climate-assessment-reverse-constraint
  "Wikidata / SensibLaw review"
  "statement shape, qualifier/reference completeness, source inspection, migration semantics and scientific claim adequacy remain distinct"
  false

libraryConstraint : ClimateAssessmentReverseConstraint
libraryConstraint = climate-assessment-reverse-constraint
  "Dewey / QID / DOI navigation"
  "one concept may have multiple library classifications; entity identity, shelf coordinate and source identity remain separate"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data ReviewWordMeansSameConsumer : Set where
data AssessmentReportCreatesIndependentEvidence : Set where
data AssessmentReportCreatesTruth : Set where
data CleanStatementCreatesScientificAdequacy : Set where
data P854CreatesSourceVerification : Set where
data ClimateQidCreatesOneDeweyParent : Set where
data DoiCreatesConsensus : Set where

reviewWordDoesNotCreateSameConsumer : ReviewWordMeansSameConsumer → ⊥
reviewWordDoesNotCreateSameConsumer ()

assessmentReportDoesNotCreateIndependentEvidence : AssessmentReportCreatesIndependentEvidence → ⊥
assessmentReportDoesNotCreateIndependentEvidence ()

assessmentReportDoesNotCreateTruth : AssessmentReportCreatesTruth → ⊥
assessmentReportDoesNotCreateTruth ()

cleanStatementDoesNotCreateScientificAdequacy : CleanStatementCreatesScientificAdequacy → ⊥
cleanStatementDoesNotCreateScientificAdequacy ()

p854DoesNotCreateSourceVerification : P854CreatesSourceVerification → ⊥
p854DoesNotCreateSourceVerification ()

climateQidDoesNotCreateOneDeweyParent : ClimateQidCreatesOneDeweyParent → ⊥
climateQidDoesNotCreateOneDeweyParent ()

doiDoesNotCreateConsensus : DoiCreatesConsensus → ⊥
doiDoesNotCreateConsensus ()

record ClimateAssessmentEvidenceIndependenceBoundary : Set where
  constructor climate-assessment-evidence-independence-boundary
  field
    climateAndReportQidsAttached : Bool
    multipleClimateDeweyCoordinatesRetained : Bool
    ipccReportDoiAndSourceRoleRetained : Bool
    reviewConsumerSemanticsSeparated : Bool
    assessmentConclusionSeparatedFromEvidenceGenealogy : Bool
    wikidataStatementShapeSeparatedFromScientificClaimAdequacy : Bool
    dependencySynthesisAtomicAndSensibLawOwnersReused : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open ClimateAssessmentEvidenceIndependenceBoundary public

canonicalClimateAssessmentEvidenceIndependenceBoundary :
  ClimateAssessmentEvidenceIndependenceBoundary
canonicalClimateAssessmentEvidenceIndependenceBoundary =
  climate-assessment-evidence-independence-boundary
    true true true true true true true true false
