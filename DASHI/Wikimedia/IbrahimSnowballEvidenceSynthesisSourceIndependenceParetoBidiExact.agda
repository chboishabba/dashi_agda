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
import DASHI.Wikimedia.IbrahimSnowballLearningMemoryTraumaReplicationConsensusBidiExact as Prior
import DASHI.Wikimedia.SensibLawSourceUnitReviewHandoffExact as SLR

------------------------------------------------------------------------
-- IBRAHIM / DEWEY PARETO FRONTIER
-- evidence synthesis <-> primary/secondary source roles <-> citation genealogy
-- <-> source independence <-> replication/corroboration <-> consensus.
--
-- High-alpha seam: the same dependency error appears in scientific replication,
-- systematic reviews, media/OSINT copying, generated testimony and expert
-- consensus.  Multiplicity is not independence; review/synthesis status is not
-- primary evidence; a citation chain is not a new observation.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim evidence-synthesis/source-independence Pareto BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create source independence, primary-evidence status, synthesis validity, replication success, consensus or truth")

systematicReviewQid : Identity.ExternalIdentityDemand
systematicReviewQid = mkQid "systematic review" "Q1504425"

metaAnalysisQid : Identity.ExternalIdentityDemand
metaAnalysisQid = mkQid "meta-analysis" "Q815382"

literatureReviewQid : Identity.ExternalIdentityDemand
literatureReviewQid = mkQid "literature review" "Q2412849"

primarySourceQid : Identity.ExternalIdentityDemand
primarySourceQid = mkQid "primary source" "Q112754"

secondarySourceQid : Identity.ExternalIdentityDemand
secondarySourceQid = mkQid "secondary source" "Q905511"

replicationCrisisQid : Identity.ExternalIdentityDemand
replicationCrisisQid = mkQid "replication crisis" "Q25303778"

evidenceSynthesisQid : Identity.ExternalIdentityDemand
evidenceSynthesisQid = Identity.mkOptionalIdentityDemand
  "Ibrahim evidence-synthesis/source-independence Pareto BIDI"
  "external concept identity"
  "generic evidence synthesis"
  Identity.wikidataQid
  (Identity.unresolved
    "a 2026 Wikidata evidence-synthesis item was inspected but is a recent neologism entry; no mature generic QID promoted here; systematic review Q1504425 and meta-analysis Q815382 remain exact neighbouring identities")

sourceIndependenceQid : Identity.ExternalIdentityDemand
sourceIndependenceQid = Identity.mkOptionalIdentityDemand
  "Ibrahim evidence-synthesis/source-independence Pareto BIDI"
  "external concept identity"
  "source independence / common-source dependence"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact stable single Wikidata concept promoted; dependence is retained as a provenance relation rather than manufactured from a nearby concept")

------------------------------------------------------------------------
-- Dewey coordinates: only inspected values are promoted.
------------------------------------------------------------------------

metaAnalysisDewey : Dewey.DeweyCoordinate
metaAnalysisDewey = Dewey.mkVerifiedDewey
  "meta-analysis"
  "519.53"
  "Wikidata Q815382 DDC statement inspected 2026-09-11; stated in GND"

systematicReviewDewey : Dewey.DeweyCoordinate
systematicReviewDewey = Dewey.mkUnresolvedDewey
  "systematic review"
  "no exact DDC statement found on inspected Q1504425 page"

primarySourceDewey : Dewey.DeweyCoordinate
primarySourceDewey = Dewey.mkUnresolvedDewey
  "primary source"
  "inspected Q112754 carries Library of Congress classification D5-D5.5, not an exact DDC value; do not convert classification systems"

sourceIndependenceDewey : Dewey.DeweyCoordinate
sourceIndependenceDewey = Dewey.mkUnresolvedDewey
  "source independence"
  "relation/provenance concept retained without an invented shelf coordinate"

------------------------------------------------------------------------
-- DOI/primary scholarship.  Each source owns only its bounded claim.
------------------------------------------------------------------------

snyderReviewMethodSource : Attribution.AttributedSource
snyderReviewMethodSource = Attribution.mkDOISource
  "Hannah Snyder"
  "Literature review as a research methodology: An overview and guidelines"
  "Journal of Business Research 104, 333-339"
  "2019"
  "10.1016/j.jbusres.2019.07.039"
  "https://doi.org/10.1016/j.jbusres.2019.07.039"
  Attribution.academicArticleSource
  "review-methodology source distinguishing literature-review approaches; supports systematic-review/meta-analysis role separation, not truth-by-review-status"
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
  "philosophy/formal analysis of evidential variety and graded source independence; source dependence is not reducible to raw source count"
  Attribution.publicAttribution

pavlovicCitationAccuracySource : Attribution.AttributedSource
pavlovicCitationAccuracySource = Attribution.mkDOISource
  "Vedrana Pavlovic; Tracey Weissgerber; Dejana Stanisavljevic; Tatjana Pekmezovic; Ognjen Milicevic; Jelena Milin Lazovic; Andja Cirkovic; Marko Savic; Nina Rajovic; Pavle Piperac; Nemanja Djuric; Petar Madzarevic; Ana Dimitrijevic; Simona Randjelovic; Emilija Nestorovic; Remi Akinyombo; Andrija Pavlovic; Ranine Ghamrawi; Vesna Garovic; Natasa Milic"
  "How accurate are citations of frequently cited papers in biomedical literature?"
  "Clinical Science 135(5), 671-681"
  "2021"
  "10.1042/CS20201573"
  "https://doi.org/10.1042/CS20201573"
  Attribution.academicArticleSource
  "empirical audit of citation accuracy; documents chains of inaccurate citation and motivates inspecting the primary source rather than counting derivative citations"
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
  "commentary/meta-research source on quotation error and citation copying; supports citation genealogy as an evidentiary-dependence concern"
  Attribution.publicAttribution

youngSourceIndependencePolarizationSource : Attribution.AttributedSource
youngSourceIndependencePolarizationSource = Attribution.mkDOISource
  "David J. Young; Jens Koed Madsen; Lee H. de-Wit"
  "Belief polarization can be caused by disagreements over source independence: Computational modelling, experimental evidence, and applicability to real-world politics"
  "Cognition 259, 106126"
  "2025"
  "10.1016/j.cognition.2025.106126"
  "https://doi.org/10.1016/j.cognition.2025.106126"
  Attribution.academicArticleSource
  "models and tests perceived testimonial-source independence as a mechanism affecting belief updating; does not imply every political disagreement is caused by source-independence judgments"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- SensibLaw reuse: review packet/runtime handoff preserves revision and anchors
-- but does not create authority or semantic promotion.
------------------------------------------------------------------------

sensibLawSLRBoundary : SLR.SensibLawHandoffBoundary
sensibLawSLRBoundary = SLR.canonicalSensibLawHandoffBoundary

priorReplicationBoundary : Prior.LearningMemoryTraumaReplicationConsensusBoundary
priorReplicationBoundary = Prior.canonicalLearningMemoryTraumaReplicationConsensusBoundary

------------------------------------------------------------------------
-- Regression 1: evidence-item count cannot recover source independence.
------------------------------------------------------------------------

data SynthesisCase : Set where
  sameEvidenceCountIndependentOrigins sameEvidenceCountCopiedOrigin : SynthesisCase

data EvidenceCountSurface : Set where sameEvidenceMultiplicity : EvidenceCountSurface
data SourceGenealogy : Set where independentOrigins commonCopiedOrigin : SourceGenealogy

evidenceCountSurface : SynthesisCase → EvidenceCountSurface
evidenceCountSurface _ = sameEvidenceMultiplicity

sourceGenealogy : SynthesisCase → SourceGenealogy
sourceGenealogy sameEvidenceCountIndependentOrigins = independentOrigins
sourceGenealogy sameEvidenceCountCopiedOrigin = commonCopiedOrigin

countIndependenceDefect : INF.NonFactorabilityWitness evidenceCountSurface sourceGenealogy
countIndependenceDefect = INF.nonFactorabilityWitness
  sameEvidenceCountIndependentOrigins sameEvidenceCountCopiedOrigin refl (λ ())

evidenceMultiplicityCannotFactorSourceIndependence :
  INF.FactorsThrough evidenceCountSurface sourceGenealogy → ⊥
evidenceMultiplicityCannotFactorSourceIndependence =
  INF.witnessRulesOutEveryFlatFactorisation countIndependenceDefect

------------------------------------------------------------------------
-- Regression 2: review/synthesis classification cannot recover primary-source
-- inspection or source authority.
------------------------------------------------------------------------

data ReviewCase : Set where
  sameSystematicReviewPrimaryInspected sameSystematicReviewPrimaryNotInspected : ReviewCase

data ReviewSurface : Set where sameSystematicReviewLabel : ReviewSurface
data PrimaryInspection : Set where primaryInspected primaryNotInspected : PrimaryInspection

reviewSurface : ReviewCase → ReviewSurface
reviewSurface _ = sameSystematicReviewLabel

primaryInspection : ReviewCase → PrimaryInspection
primaryInspection sameSystematicReviewPrimaryInspected = primaryInspected
primaryInspection sameSystematicReviewPrimaryNotInspected = primaryNotInspected

reviewInspectionDefect : INF.NonFactorabilityWitness reviewSurface primaryInspection
reviewInspectionDefect = INF.nonFactorabilityWitness
  sameSystematicReviewPrimaryInspected sameSystematicReviewPrimaryNotInspected refl (λ ())

systematicReviewLabelCannotFactorPrimaryInspection :
  INF.FactorsThrough reviewSurface primaryInspection → ⊥
systematicReviewLabelCannotFactorPrimaryInspection =
  INF.witnessRulesOutEveryFlatFactorisation reviewInspectionDefect

------------------------------------------------------------------------
-- Regression 3: citation agreement cannot recover claim support.
------------------------------------------------------------------------

data CitationCase : Set where
  sameCitationChainAccurate sameCitationChainDistorted : CitationCase

data CitationSurface : Set where sameCitationAgreement : CitationSurface
data SupportStatus : Set where primarySupportsClaim primaryDoesNotSupportClaim : SupportStatus

citationSurface : CitationCase → CitationSurface
citationSurface _ = sameCitationAgreement

supportStatus : CitationCase → SupportStatus
supportStatus sameCitationChainAccurate = primarySupportsClaim
supportStatus sameCitationChainDistorted = primaryDoesNotSupportClaim

citationSupportDefect : INF.NonFactorabilityWitness citationSurface supportStatus
citationSupportDefect = INF.nonFactorabilityWitness
  sameCitationChainAccurate sameCitationChainDistorted refl (λ ())

citationAgreementCannotFactorPrimarySupport :
  INF.FactorsThrough citationSurface supportStatus → ⊥
citationAgreementCannotFactorPrimarySupport =
  INF.witnessRulesOutEveryFlatFactorisation citationSupportDefect

------------------------------------------------------------------------
-- Regression 4: consensus/review agreement cannot recover methodological
-- independence or proposition truth.
------------------------------------------------------------------------

data ConsensusDependenceCase : Set where
  sameConsensusIndependentMethods sameConsensusSharedDependency : ConsensusDependenceCase

data ConsensusSurface : Set where sameConsensusSummary : ConsensusSurface
data MethodDependence : Set where methodologicallyVaried commonMethodDependency : MethodDependence

consensusSurface : ConsensusDependenceCase → ConsensusSurface
consensusSurface _ = sameConsensusSummary

methodDependence : ConsensusDependenceCase → MethodDependence
methodDependence sameConsensusIndependentMethods = methodologicallyVaried
methodDependence sameConsensusSharedDependency = commonMethodDependency

consensusDependenceDefect : INF.NonFactorabilityWitness consensusSurface methodDependence
consensusDependenceDefect = INF.nonFactorabilityWitness
  sameConsensusIndependentMethods sameConsensusSharedDependency refl (λ ())

consensusSurfaceCannotFactorMethodIndependence :
  INF.FactorsThrough consensusSurface methodDependence → ⊥
consensusSurfaceCannotFactorMethodIndependence =
  INF.witnessRulesOutEveryFlatFactorisation consensusDependenceDefect

------------------------------------------------------------------------
-- Reverse BIDI constraints / Pareto fan-out.
------------------------------------------------------------------------

record SynthesisReverseConstraint : Set where
  constructor synthesis-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open SynthesisReverseConstraint public

scienceConstraint : SynthesisReverseConstraint
scienceConstraint = synthesis-reverse-constraint
  "Science / replication / consensus"
  "result count, independent origin, methodological variety, reproducibility, synthesis method, uncertainty and consensus remain distinct"
  false

informationConstraint : SynthesisReverseConstraint
informationConstraint = synthesis-reverse-constraint
  "Library / information / citation graph"
  "citation edge, copied reference, inspected primary source, accurate claim support, source genealogy and review classification remain distinct"
  false

sensibLawConstraint : SynthesisReverseConstraint
sensibLawConstraint = synthesis-reverse-constraint
  "SensibLaw / SLR"
  "source-unit revision, anchor, review packet, follow receipt, source authority, primary inspection and semantic promotion remain distinct"
  false

osintMediaConstraint : SynthesisReverseConstraint
osintMediaConstraint = synthesis-reverse-constraint
  "OSINT / media / alternative media"
  "number of reports, syndication/copying, common upstream source, direct observation, corroboration and truth remain distinct"
  false

psychologyConstraint : SynthesisReverseConstraint
psychologyConstraint = synthesis-reverse-constraint
  "Testimony / cognition / polarization"
  "agreement count, perceived source independence, actual provenance independence, credibility and proposition truth remain distinct"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data ManySourcesMeanIndependent : Set where
data SystematicReviewMeansPrimaryInspected : Set where
data CitationMeansPrimarySupport : Set where
data SecondarySourceBecomesPrimary : Set where
data MetaAnalysisMeansTruth : Set where
data ConsensusMeansIndependentMethods : Set where
data SLRPacketCreatesAuthority : Set where
data QidCreatesSourceRole : Set where
data DeweyCreatesEvidenceHierarchy : Set where

manySourcesDoNotCreateIndependence : ManySourcesMeanIndependent → ⊥
manySourcesDoNotCreateIndependence ()

systematicReviewDoesNotCreatePrimaryInspection : SystematicReviewMeansPrimaryInspected → ⊥
systematicReviewDoesNotCreatePrimaryInspection ()

citationDoesNotCreatePrimarySupport : CitationMeansPrimarySupport → ⊥
citationDoesNotCreatePrimarySupport ()

secondarySourceDoesNotBecomePrimary : SecondarySourceBecomesPrimary → ⊥
secondarySourceDoesNotBecomePrimary ()

metaAnalysisDoesNotCreateTruth : MetaAnalysisMeansTruth → ⊥
metaAnalysisDoesNotCreateTruth ()

consensusDoesNotCreateIndependentMethods : ConsensusMeansIndependentMethods → ⊥
consensusDoesNotCreateIndependentMethods ()

slrPacketDoesNotCreateAuthority : SLRPacketCreatesAuthority → ⊥
slrPacketDoesNotCreateAuthority ()

qidDoesNotCreateSourceRole : QidCreatesSourceRole → ⊥
qidDoesNotCreateSourceRole ()

deweyDoesNotCreateEvidenceHierarchy : DeweyCreatesEvidenceHierarchy → ⊥
deweyDoesNotCreateEvidenceHierarchy ()

record EvidenceSynthesisSourceIndependenceBoundary : Set where
  constructor evidence-synthesis-source-independence-boundary
  field
    primarySecondaryQidsRetained : Bool
    systematicReviewMetaAnalysisQidsRetained : Bool
    weakEvidenceSynthesisQidLeftUnresolved : Bool
    metaAnalysisDeweyRetained : Bool
    doiPrimaryScholarshipRetained : Bool
    canonicalLinksRetained : Bool
    multiplicitySeparatedFromIndependence : Bool
    citationAgreementSeparatedFromPrimarySupport : Bool
    synthesisClassificationSeparatedFromPrimaryInspection : Bool
    consensusSeparatedFromMethodIndependence : Bool
    sensibLawSLRAuthorityBoundaryReused : Bool
    reverseBidiParetoFanoutPresent : Bool
    presentAxisVocabularyClaimedComplete : Bool
open EvidenceSynthesisSourceIndependenceBoundary public

canonicalEvidenceSynthesisSourceIndependenceBoundary : EvidenceSynthesisSourceIndependenceBoundary
canonicalEvidenceSynthesisSourceIndependenceBoundary =
  evidence-synthesis-source-independence-boundary
    true true true true true true true true true true true true false
