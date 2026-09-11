module DASHI.Wikimedia.IbrahimSnowballEvidenceSynthesisSourceIndependenceParetoBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballSystematicReviewMetaAnalysisPublicationBiasBidiExact as Review
import DASHI.Wikimedia.IbrahimSnowballSourceGenealogyIndependenceEvidenceSynthesisBidiExact as Genealogy

------------------------------------------------------------------------
-- THIN PARETO DELTA AFTER LIVE-BRANCH QUOTIENTING
--
-- Broad evidence-synthesis, source-genealogy, publication-bias, primary-source,
-- information-cascade and replication-dependence machinery already exists on
-- this branch.  This file retains only the surviving uncovered coordinates:
--   * literature-review + secondary-source + replication-crisis identities,
--   * verified meta-analysis DDC 519.53,
--   * citation agreement != primary-source claim support,
--   * perceived source independence != actual provenance independence.
--
-- QID / DOI / canonical links / Dewey remain attribution and navigation
-- coordinates; none creates truth, independence, source role or authority.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim evidence-synthesis/source-independence Pareto delta"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create truth, source role, independence, review quality or authority")

systematicReviewQid : Identity.ExternalIdentityDemand
systematicReviewQid = Review.systematicReviewQid

metaAnalysisQid : Identity.ExternalIdentityDemand
metaAnalysisQid = Review.metaAnalysisQid

primarySourceQid : Identity.ExternalIdentityDemand
primarySourceQid = Genealogy.primarySourceQid

literatureReviewQid : Identity.ExternalIdentityDemand
literatureReviewQid = mkQid "literature review" "Q2412849"

secondarySourceQid : Identity.ExternalIdentityDemand
secondarySourceQid = mkQid "secondary source" "Q905511"

replicationCrisisQid : Identity.ExternalIdentityDemand
replicationCrisisQid = mkQid "replication crisis" "Q25303778"

sourceIndependenceQid : Identity.ExternalIdentityDemand
sourceIndependenceQid = Identity.mkOptionalIdentityDemand
  "Ibrahim evidence-synthesis/source-independence Pareto delta"
  "external concept identity"
  "source independence / common-source dependence"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact stable single Wikidata identity promoted; provenance independence remains a typed relation")

------------------------------------------------------------------------
-- Dewey delta.
------------------------------------------------------------------------

metaAnalysisDewey : Dewey.DeweyCoordinate
metaAnalysisDewey = Dewey.mkVerifiedDewey
  "meta-analysis"
  "519.53"
  "Wikidata Q815382 DDC statement inspected 2026-09-11; stated in Integrated Authority File/GND"

literatureReviewDewey : Dewey.DeweyCoordinate
literatureReviewDewey = Dewey.mkUnresolvedDewey
  "literature review"
  "Q2412849 verified; no exact inspected DDC value promoted"

secondarySourceDewey : Dewey.DeweyCoordinate
secondarySourceDewey = Dewey.mkUnresolvedDewey
  "secondary source"
  "Q905511 verified; no exact inspected DDC value promoted"

------------------------------------------------------------------------
-- DOI / canonical-source attribution for the surviving residuals.
------------------------------------------------------------------------

pavlovicCitationAccuracySource : Attribution.AttributedSource
pavlovicCitationAccuracySource = Attribution.mkDOISource
  "Vedrana Pavlovic; Tracey Weissgerber; Dejana Stanisavljevic; Tatjana Pekmezovic; Ognjen Milicevic; Jelena Milin Lazovic; Andja Cirkovic; Marko Savic; Nina Rajovic; Pavle Piperac; Nemanja Djuric; Petar Madzarevic; Ana Dimitrijevic; Simona Randjelovic; Emilija Nestorovic; Remi Akinyombo; Andrija Pavlovic; Ranine Ghamrawi; Vesna Garovic; Natasa Milic"
  "How accurate are citations of frequently cited papers in biomedical literature?"
  "Clinical Science 135(5), 671-681"
  "2021"
  "10.1042/CS20201573"
  "https://doi.org/10.1042/CS20201573"
  Attribution.academicArticleSource
  "empirical citation-accuracy audit; supports checking claim-to-primary-source support and citation-chain errors, not distrust of citation as such"
  Attribution.publicAttribution

ioannidisCitationCopyingSource : Attribution.AttributedSource
ioannidisCitationCopyingSource = Attribution.mkDOISource
  "John P. A. Ioannidis"
  "Massive citations to misleading methods and research tools: Matthew effect, quotation error and citation copying"
  "European Journal of Epidemiology 33(11), 1021-1023"
  "2018"
  "10.1007/s10654-018-0449-x"
  "https://doi.org/10.1007/s10654-018-0449-x"
  Attribution.academicArticleSource
  "meta-research commentary on quotation error and citation copying; supports citation genealogy as a dependence concern"
  Attribution.publicAttribution

youngSourceIndependenceSource : Attribution.AttributedSource
youngSourceIndependenceSource = Attribution.mkDOISource
  "David J. Young; Jens Koed Madsen; Lee H. de-Wit"
  "Belief polarization can be caused by disagreements over source independence: Computational modelling, experimental evidence, and applicability to real-world politics"
  "Cognition 259, 106126"
  "2025"
  "10.1016/j.cognition.2025.106126"
  "https://doi.org/10.1016/j.cognition.2025.106126"
  Attribution.academicArticleSource
  "models and tests perceived testimonial-source independence as a mechanism in belief updating; perceived independence remains distinct from actual provenance independence"
  Attribution.publicAttribution

landesSourceIndependenceSource : Attribution.AttributedSource
landesSourceIndependenceSource = Attribution.mkDOISource
  "Jürgen Landes"
  "The variety of evidence thesis and its independence of degrees of independence"
  "Synthese 198, 10611-10641"
  "2021"
  "10.1007/s11229-020-02738-5"
  "https://doi.org/10.1007/s11229-020-02738-5"
  Attribution.academicArticleSource
  "formal/philosophical analysis of degrees of source independence; raw multiplicity and provenance independence remain distinct"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Exact reuse: no parallel evidence-synthesis ontology.
------------------------------------------------------------------------

reviewBoundary : Review.SystematicReviewMetaAnalysisBoundary
reviewBoundary = Review.canonicalSystematicReviewMetaAnalysisBoundary

genealogyBoundary : Genealogy.SourceGenealogyIndependenceEvidenceSynthesisBoundary
genealogyBoundary = Genealogy.canonicalSourceGenealogyIndependenceEvidenceSynthesisBoundary

------------------------------------------------------------------------
-- Regression 1: citation agreement cannot recover direct primary support.
------------------------------------------------------------------------

data CitationCase : Set where
  sameCitationAgreementPrimarySupports sameCitationAgreementPrimaryDoesNotSupport : CitationCase

data CitationSurface : Set where sameCitationAgreement : CitationSurface
data PrimarySupport : Set where primarySupportsClaim primaryDoesNotSupportClaim : PrimarySupport

citationSurface : CitationCase → CitationSurface
citationSurface _ = sameCitationAgreement

primarySupport : CitationCase → PrimarySupport
primarySupport sameCitationAgreementPrimarySupports = primarySupportsClaim
primarySupport sameCitationAgreementPrimaryDoesNotSupport = primaryDoesNotSupportClaim

citationSupportDefect : INF.NonFactorabilityWitness citationSurface primarySupport
citationSupportDefect = INF.nonFactorabilityWitness
  sameCitationAgreementPrimarySupports sameCitationAgreementPrimaryDoesNotSupport refl (λ ())

citationAgreementCannotFactorPrimarySupport :
  INF.FactorsThrough citationSurface primarySupport → ⊥
citationAgreementCannotFactorPrimarySupport =
  INF.witnessRulesOutEveryFlatFactorisation citationSupportDefect

------------------------------------------------------------------------
-- Regression 2: perceived source independence cannot recover actual provenance
-- independence.  The psychological update coordinate and the evidentiary
-- genealogy coordinate are distinct even when both matter to a consumer.
------------------------------------------------------------------------

data IndependenceCase : Set where
  samePerceivedIndependentActuallyIndependent samePerceivedIndependentActuallyDependent : IndependenceCase

data PerceivedIndependence : Set where perceivedAsIndependent : PerceivedIndependence
data ProvenanceIndependence : Set where actuallyIndependent commonSourceDependent : ProvenanceIndependence

perceivedIndependence : IndependenceCase → PerceivedIndependence
perceivedIndependence _ = perceivedAsIndependent

provenanceIndependence : IndependenceCase → ProvenanceIndependence
provenanceIndependence samePerceivedIndependentActuallyIndependent = actuallyIndependent
provenanceIndependence samePerceivedIndependentActuallyDependent = commonSourceDependent

perceptionProvenanceDefect : INF.NonFactorabilityWitness perceivedIndependence provenanceIndependence
perceptionProvenanceDefect = INF.nonFactorabilityWitness
  samePerceivedIndependentActuallyIndependent samePerceivedIndependentActuallyDependent refl (λ ())

perceivedIndependenceCannotFactorActualProvenance :
  INF.FactorsThrough perceivedIndependence provenanceIndependence → ⊥
perceivedIndependenceCannotFactorActualProvenance =
  INF.witnessRulesOutEveryFlatFactorisation perceptionProvenanceDefect

------------------------------------------------------------------------
-- Reverse Pareto fan-out.
------------------------------------------------------------------------

record ParetoReverseConstraint : Set where
  constructor pareto-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open ParetoReverseConstraint public

informationConstraint : ParetoReverseConstraint
informationConstraint = pareto-reverse-constraint
  "Information / bibliography / review"
  "citation agreement, direct primary-source support, review classification, secondary-source role and source genealogy remain distinct"
  false

psychologyConstraint : ParetoReverseConstraint
psychologyConstraint = pareto-reverse-constraint
  "Cognition / testimony / polarization"
  "perceived source independence, actual provenance independence, credibility, agreement and belief update remain distinct"
  false

scienceConstraint : ParetoReverseConstraint
scienceConstraint = pareto-reverse-constraint
  "Science / meta-analysis / replication"
  "meta-analysis identity, DDC classification, included-study count, dependence, replication status, synthesis result and truth remain distinct"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data CitationAgreementMeansPrimarySupport : Set where
data PerceivedIndependenceMeansActualIndependence : Set where
data SecondarySourceMeansWeakEvidence : Set where
data MetaAnalysisDeweyMeansTruth : Set where
data QidCreatesSourceRole : Set where

citationAgreementDoesNotCreatePrimarySupport : CitationAgreementMeansPrimarySupport → ⊥
citationAgreementDoesNotCreatePrimarySupport ()

perceivedIndependenceDoesNotCreateActualIndependence : PerceivedIndependenceMeansActualIndependence → ⊥
perceivedIndependenceDoesNotCreateActualIndependence ()

secondarySourceDoesNotMeanWeakEvidence : SecondarySourceMeansWeakEvidence → ⊥
secondarySourceDoesNotMeanWeakEvidence ()

metaAnalysisDeweyDoesNotCreateTruth : MetaAnalysisDeweyMeansTruth → ⊥
metaAnalysisDeweyDoesNotCreateTruth ()

qidDoesNotCreateSourceRole : QidCreatesSourceRole → ⊥
qidDoesNotCreateSourceRole ()

record EvidenceSynthesisSourceIndependenceParetoBoundary : Set where
  constructor evidence-synthesis-source-independence-pareto-boundary
  field
    broadCanonicalOwnersReused : Bool
    literatureReviewSecondarySourceReplicationCrisisQidsAttached : Bool
    exactMetaAnalysisDeweyAttached : Bool
    doiCanonicalSourcesRetained : Bool
    citationAgreementSeparatedFromPrimarySupport : Bool
    perceivedIndependenceSeparatedFromActualProvenance : Bool
    qidDeweySourceRoleTruthSeparated : Bool
    reverseParetoFanoutPresent : Bool
    presentAxisVocabularyClaimedComplete : Bool
open EvidenceSynthesisSourceIndependenceParetoBoundary public

canonicalEvidenceSynthesisSourceIndependenceParetoBoundary :
  EvidenceSynthesisSourceIndependenceParetoBoundary
canonicalEvidenceSynthesisSourceIndependenceParetoBoundary =
  evidence-synthesis-source-independence-pareto-boundary
    true true true true true true true true false
