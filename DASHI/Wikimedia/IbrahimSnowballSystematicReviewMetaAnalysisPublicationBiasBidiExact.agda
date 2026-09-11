module DASHI.Wikimedia.IbrahimSnowballSystematicReviewMetaAnalysisPublicationBiasBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballLearningMemoryTraumaReplicationConsensusBidiExact as Prior
import DASHI.Wikimedia.SensibLawSourceUnitReviewHandoffExact as SensibLawReview

------------------------------------------------------------------------
-- IBRAHIM / DEWEY / SENSIBLAW REVIEW-SYNTHESIS CONTINUATION
--
-- corroboration/replication -> systematic review -> meta-analysis -> consensus
-- must retain source genealogy, publication multiplicity, dataset/method/code
-- dependence, eligibility decisions, reporting quality and publication bias.
--
-- QID identifies the external concept. DOI/canonical links identify source
-- manifestations. Dewey is a library-classification coordinate when inspected.
-- None of these creates independence, evidentiary weight, consensus or truth.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim systematic-review/meta-analysis/publication-bias BIDI"
  "verified external concept identity"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create review quality, independence, pooled validity, consensus or truth")

systematicReviewQid : Identity.ExternalIdentityDemand
systematicReviewQid = mkQid "systematic review" "Q1504425"

metaAnalysisQid : Identity.ExternalIdentityDemand
metaAnalysisQid = mkQid "meta-analysis" "Q815382"

publicationBiasQid : Identity.ExternalIdentityDemand
publicationBiasQid = mkQid "publication bias" "Q919364"

prismaQid : Identity.ExternalIdentityDemand
prismaQid = mkQid
  "Preferred Reporting Items for Systematic Reviews and Meta-Analyses (PRISMA)"
  "Q7239841"

evidenceSynthesisQid : Identity.ExternalIdentityDemand
evidenceSynthesisQid = Identity.mkOptionalIdentityDemand
  "Ibrahim systematic-review/meta-analysis/publication-bias BIDI"
  "external concept identity"
  "evidence synthesis"
  Identity.wikidataQid
  (Identity.unresolved
    "systematic review Q1504425 explicitly links to evidence synthesis in inspected Wikidata, but no exact standalone evidence-synthesis QID was promoted in this pass")

------------------------------------------------------------------------
-- Dewey stays explicit but unresolved unless an exact inspected DDC statement
-- is available.  Review methodology must not inherit a shelf number by analogy.
------------------------------------------------------------------------

systematicReviewDewey : Dewey.DeweyCoordinate
systematicReviewDewey = Dewey.mkUnresolvedDewey
  "systematic review"
  "no exact inspected DDC value promoted in this pass"

metaAnalysisDewey : Dewey.DeweyCoordinate
metaAnalysisDewey = Dewey.mkUnresolvedDewey
  "meta-analysis"
  "no exact inspected DDC value promoted in this pass"

publicationBiasDewey : Dewey.DeweyCoordinate
publicationBiasDewey = Dewey.mkUnresolvedDewey
  "publication bias"
  "no exact inspected DDC value promoted in this pass"

------------------------------------------------------------------------
-- Source manifests / primary methodological objects.
------------------------------------------------------------------------

prisma2020BMJSource : Attribution.AttributedSource
prisma2020BMJSource = Attribution.mkDOISource
  "Matthew J. Page et al."
  "The PRISMA 2020 statement: an updated guideline for reporting systematic reviews"
  "BMJ 372:n71"
  "2021"
  "10.1136/bmj.n71"
  "https://doi.org/10.1136/bmj.n71"
  Attribution.academicArticleSource
  "primary reporting-guideline manifestation for transparent systematic-review reporting; reporting compliance does not create review truth or evidentiary independence"
  Attribution.publicAttribution

prisma2020PLOSSource : Attribution.AttributedSource
prisma2020PLOSSource = Attribution.mkDOISource
  "Matthew J. Page et al."
  "The PRISMA 2020 statement: An updated guideline for reporting systematic reviews"
  "PLOS Medicine 18(3):e1003583"
  "2021"
  "10.1371/journal.pmed.1003583"
  "https://doi.org/10.1371/journal.pmed.1003583"
  Attribution.academicArticleSource
  "parallel publication manifestation of PRISMA 2020; duplicate manifestations must not be counted as independent evidence objects"
  Attribution.publicAttribution

eggerPublicationBiasSource : Attribution.AttributedSource
eggerPublicationBiasSource = Attribution.mkDOISource
  "Matthias Egger; George Davey Smith; Martin Schneider; Christoph Minder"
  "Bias in meta-analysis detected by a simple, graphical test"
  "BMJ 315:629-634"
  "1997"
  "10.1136/bmj.315.7109.629"
  "https://doi.org/10.1136/bmj.315.7109.629"
  Attribution.academicArticleSource
  "primary methodological publication on detecting small-study/publication-bias patterns in meta-analysis; a bias test result is not itself complete causal identification of publication bias"
  Attribution.publicAttribution

wikidataReviewSource : Attribution.AttributedSource
wikidataReviewSource = Attribution.mkDOISource
  "Marçal Mora-Cantallops; Elena García-Barriocanal; Miguel-Angel Sicilia"
  "A systematic literature review on Wikidata"
  "Data Technologies and Applications 53(3), 250-268"
  "2019"
  "10.1108/DTA-12-2018-0110"
  "https://doi.org/10.1108/DTA-12-2018-0110"
  Attribution.academicArticleSource
  "bounded systematic literature review of Wikidata research; historical coverage snapshot, not authority over current Wikidata or DASHI graph semantics"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Reuse existing repo boundaries rather than replacing them.
------------------------------------------------------------------------

priorReplicationBoundary : Prior.LearningMemoryTraumaReplicationConsensusBoundary
priorReplicationBoundary = Prior.canonicalLearningMemoryTraumaReplicationConsensusBoundary

sensibLawReviewBoundary : SensibLawReview.SensibLawHandoffBoundary
sensibLawReviewBoundary = SensibLawReview.canonicalSensibLawHandoffBoundary

------------------------------------------------------------------------
-- Regression 1: publication/study count cannot recover independent evidence
-- units. Multiple papers may be parallel manifestations, shared datasets,
-- shared code/method lineage, overlapping samples, or genuinely independent.
------------------------------------------------------------------------

data ReviewMultiplicityCase : Set where
  sameIncludedCountIndependentUnits sameIncludedCountDependentUnits : ReviewMultiplicityCase

data IncludedCountSurface : Set where sameIncludedStudyCount : IncludedCountSurface
data EvidenceIndependence : Set where independentEvidenceUnits dependentEvidenceUnits : EvidenceIndependence

includedCountSurface : ReviewMultiplicityCase → IncludedCountSurface
includedCountSurface _ = sameIncludedStudyCount

evidenceIndependence : ReviewMultiplicityCase → EvidenceIndependence
evidenceIndependence sameIncludedCountIndependentUnits = independentEvidenceUnits
evidenceIndependence sameIncludedCountDependentUnits = dependentEvidenceUnits

reviewIndependenceDefect : INF.NonFactorabilityWitness includedCountSurface evidenceIndependence
reviewIndependenceDefect = INF.nonFactorabilityWitness
  sameIncludedCountIndependentUnits sameIncludedCountDependentUnits refl (λ ())

includedCountCannotFactorIndependentEvidenceUnits :
  INF.FactorsThrough includedCountSurface evidenceIndependence → ⊥
includedCountCannotFactorIndependentEvidenceUnits =
  INF.witnessRulesOutEveryFlatFactorisation reviewIndependenceDefect

------------------------------------------------------------------------
-- Regression 2: same pooled/meta-analytic estimate cannot recover selection or
-- publication-bias state.
------------------------------------------------------------------------

data PoolCase : Set where
  samePooledEstimateLowSelectionConcern samePooledEstimateHighSelectionConcern : PoolCase

data PooledSurface : Set where samePooledEstimate : PooledSurface
data SelectionBiasStatus : Set where lowerSelectionConcern higherSelectionConcern : SelectionBiasStatus

pooledSurface : PoolCase → PooledSurface
pooledSurface _ = samePooledEstimate

selectionBiasStatus : PoolCase → SelectionBiasStatus
selectionBiasStatus samePooledEstimateLowSelectionConcern = lowerSelectionConcern
selectionBiasStatus samePooledEstimateHighSelectionConcern = higherSelectionConcern

pooledBiasDefect : INF.NonFactorabilityWitness pooledSurface selectionBiasStatus
pooledBiasDefect = INF.nonFactorabilityWitness
  samePooledEstimateLowSelectionConcern samePooledEstimateHighSelectionConcern refl (λ ())

pooledEstimateCannotFactorPublicationBiasStatus :
  INF.FactorsThrough pooledSurface selectionBiasStatus → ⊥
pooledEstimateCannotFactorPublicationBiasStatus =
  INF.witnessRulesOutEveryFlatFactorisation pooledBiasDefect

------------------------------------------------------------------------
-- Regression 3: transparent reporting/PRISMA compliance cannot recover truth.
------------------------------------------------------------------------

data ReportingCase : Set where
  sameTransparentReportingClaimTrue sameTransparentReportingClaimFalse : ReportingCase

data ReportingSurface : Set where sameTransparentReviewReporting : ReportingSurface
data ReviewTruth : Set where reviewClaimTrue reviewClaimFalse : ReviewTruth

reportingSurface : ReportingCase → ReportingSurface
reportingSurface _ = sameTransparentReviewReporting

reviewTruth : ReportingCase → ReviewTruth
reviewTruth sameTransparentReportingClaimTrue = reviewClaimTrue
reviewTruth sameTransparentReportingClaimFalse = reviewClaimFalse

reportingTruthDefect : INF.NonFactorabilityWitness reportingSurface reviewTruth
reportingTruthDefect = INF.nonFactorabilityWitness
  sameTransparentReportingClaimTrue sameTransparentReportingClaimFalse refl (λ ())

reportingComplianceCannotFactorReviewTruth :
  INF.FactorsThrough reportingSurface reviewTruth → ⊥
reportingComplianceCannotFactorReviewTruth =
  INF.witnessRulesOutEveryFlatFactorisation reportingTruthDefect

------------------------------------------------------------------------
-- Regression 4: review inclusion cannot recover evidentiary weight/authority.
------------------------------------------------------------------------

data InclusionCase : Set where
  sameIncludedStatusHighWeight sameIncludedStatusLowWeight : InclusionCase

data InclusionSurface : Set where sameIncludedInReview : InclusionSurface
data EvidentiaryWeight : Set where higherWeight lowerWeight : EvidentiaryWeight

inclusionSurface : InclusionCase → InclusionSurface
inclusionSurface _ = sameIncludedInReview

evidentiaryWeight : InclusionCase → EvidentiaryWeight
evidentiaryWeight sameIncludedStatusHighWeight = higherWeight
evidentiaryWeight sameIncludedStatusLowWeight = lowerWeight

inclusionWeightDefect : INF.NonFactorabilityWitness inclusionSurface evidentiaryWeight
inclusionWeightDefect = INF.nonFactorabilityWitness
  sameIncludedStatusHighWeight sameIncludedStatusLowWeight refl (λ ())

reviewInclusionCannotFactorEvidentiaryWeight :
  INF.FactorsThrough inclusionSurface evidentiaryWeight → ⊥
reviewInclusionCannotFactorEvidentiaryWeight =
  INF.witnessRulesOutEveryFlatFactorisation inclusionWeightDefect

------------------------------------------------------------------------
-- Reverse BIDI constraints into Ibrahim parents.
------------------------------------------------------------------------

record ReviewReverseConstraint : Set where
  constructor review-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open ReviewReverseConstraint public

scienceConstraint : ReviewReverseConstraint
scienceConstraint = review-reverse-constraint
  "Science / evidence synthesis"
  "publication count, study count, independent evidence units, methodological quality, selection/publication bias, pooled estimate, uncertainty and consensus remain distinct"
  false

informationConstraint : ReviewReverseConstraint
informationConstraint = review-reverse-constraint
  "Library / information science"
  "bibliographic manifestation, work identity, duplicate/parallel publication, source genealogy, inclusion and evidentiary role remain distinct"
  false

sensibLawConstraint : ReviewReverseConstraint
sensibLawConstraint = review-reverse-constraint
  "SensibLaw / SLR review packet"
  "source unit revision, anchors, follow receipts, reviewer uncertainty, inclusion/split decision, runtime handoff and semantic promotion remain distinct"
  false

consensusConstraint : ReviewReverseConstraint
consensusConstraint = review-reverse-constraint
  "Consensus / expertise"
  "review result, expert interpretation, provenance independence, publication bias, consensus state and proposition truth remain distinct"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data MoreStudiesMeansMoreIndependentEvidence : Set where
data MetaAnalysisMeansTruth : Set where
data PRISMAComplianceMeansTruth : Set where
data ReviewInclusionMeansAuthority : Set where
data PublicationBiasTestProvesBiasCause : Set where
data QidMeansReviewQuality : Set where
data DeweyMeansEvidenceHierarchy : Set where

moreStudiesDoNotCreateIndependentEvidence : MoreStudiesMeansMoreIndependentEvidence → ⊥
moreStudiesDoNotCreateIndependentEvidence ()

metaAnalysisDoesNotMeanTruth : MetaAnalysisMeansTruth → ⊥
metaAnalysisDoesNotMeanTruth ()

prismaComplianceDoesNotMeanTruth : PRISMAComplianceMeansTruth → ⊥
prismaComplianceDoesNotMeanTruth ()

reviewInclusionDoesNotCreateAuthority : ReviewInclusionMeansAuthority → ⊥
reviewInclusionDoesNotCreateAuthority ()

biasTestDoesNotIdentifyCompleteCause : PublicationBiasTestProvesBiasCause → ⊥
biasTestDoesNotIdentifyCompleteCause ()

qidDoesNotCreateReviewQuality : QidMeansReviewQuality → ⊥
qidDoesNotCreateReviewQuality ()

deweyDoesNotCreateEvidenceHierarchy : DeweyMeansEvidenceHierarchy → ⊥
deweyDoesNotCreateEvidenceHierarchy ()

record SystematicReviewMetaAnalysisBoundary : Set where
  constructor systematic-review-meta-analysis-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    deweyUnresolvedRetainedExplicitly : Bool
    doiAndCanonicalLinksRetained : Bool
    primaryMethodologicalSourcesAttributed : Bool
    duplicateManifestationsSeparatedFromIndependentEvidence : Bool
    includedCountSeparatedFromIndependentEvidenceUnits : Bool
    pooledEstimateSeparatedFromPublicationBias : Bool
    reportingComplianceSeparatedFromTruth : Bool
    reviewInclusionSeparatedFromAuthority : Bool
    sensibLawReviewPacketBoundaryReused : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open SystematicReviewMetaAnalysisBoundary public

canonicalSystematicReviewMetaAnalysisBoundary : SystematicReviewMetaAnalysisBoundary
canonicalSystematicReviewMetaAnalysisBoundary =
  systematic-review-meta-analysis-boundary
    true true true true true true true true true true true false
