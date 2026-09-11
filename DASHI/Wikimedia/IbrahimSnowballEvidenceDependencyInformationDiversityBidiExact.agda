module DASHI.Wikimedia.IbrahimSnowballEvidenceDependencyInformationDiversityBidiExact where

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
import DASHI.Wikimedia.IbrahimSnowballTestimonyMemoryCredibilityCorroborationExpertBidiExact as Testimony
import DASHI.Wikimedia.IbrahimSnowballConspiracyDistrustAlternativeMediaBidiExact as Media
import DASHI.Wikimedia.IbrahimSnowballSocialInfluenceConsentCoercionPrimarySourcesExact as Influence

------------------------------------------------------------------------
-- IBRAHIM / SNOWBALL: EVIDENCE DEPENDENCY AND INFORMATION DIVERSITY
--
-- The prior owner already proves multiplicity != provenance independence.
-- This owner pays the next residual instead of duplicating that theorem:
-- dependency topology != evidential value, independence != reliability, and
-- surface agreement/consensus != provenance diversity.
------------------------------------------------------------------------

dependencyQid : Identity.ExternalIdentityDemand
dependencyQid = Identity.mkOptionalIdentityDemand
  "Ibrahim evidence-dependency/information-diversity BIDI"
  "external concept identity"
  "informational/evidential dependence among testimony or measurement sources"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact single QID promoted: statistical dependence, causal dependence, source dependence and social-network information dependence are not assumed identical")

dependencyDewey : Dewey.DeweyCoordinate
dependencyDewey = Dewey.mkUnresolvedDewey
  "informational/evidential dependence"
  "no exact inspected DDC value promoted; do not infer a Dewey number from probability/statistics or epistemology neighbours"

corroboratingEvidenceQid : Identity.ExternalIdentityDemand
corroboratingEvidenceQid = Testimony.corroboratingEvidenceQid

reproducibilityQid : Identity.ExternalIdentityDemand
reproducibilityQid = Prior.reproducibilityQid

scientificConsensusQid : Identity.ExternalIdentityDemand
scientificConsensusQid = Prior.scientificConsensusQid

------------------------------------------------------------------------
-- Primary/canonical source bundle.
--
-- Springer labels the article Original Research.  Its contribution is a
-- conceptual/normative analysis of dependence using Bayesian tools; citation
-- records that source role but imports no theorem authority into DASHI.
------------------------------------------------------------------------

pilditchDependencySource : Attribution.AttributedSource
pilditchDependencySource = Attribution.mkDOISource
  "Toby D. Pilditch; Ulrike Hahn; David Lagnado"
  "The problem of dependency"
  "Synthese 205, article 143"
  "2025"
  "10.1007/s11229-025-04969-w"
  "https://doi.org/10.1007/s11229-025-04969-w"
  Attribution.academicArticleSource
  "primary theoretical/original-research source analysing informational dependence among testimony and measurement, including cases where dependence can hurt or help evidential support and limits of Bayesian-network representations for social communication; does not imply that dependence is worthless or independence is reliable"
  Attribution.publicAttribution

pilditchPreprintIdentity : Identity.ExternalIdentityDemand
pilditchPreprintIdentity = Identity.mkOptionalIdentityDemand
  "Pilditch-Hahn-Lagnado dependency source"
  "preprint identity retained alongside version of record"
  "The problem of dependency preprint"
  Identity.doi
  (Identity.verified "10.31234/osf.io/d2b6e"
    "preprint DOI reported by the 2025 Synthese version of record; version-of-record DOI remains separately retained")

------------------------------------------------------------------------
-- Existing theorem reused: result/report multiplicity cannot recover source
-- independence.  This is not reproved here.
------------------------------------------------------------------------

multiplicityStillCannotFactorIndependence :
  INF.FactorsThrough Prior.replicationSurface Prior.provenanceIndependence → ⊥
multiplicityStillCannotFactorIndependence =
  Prior.replicationMultiplicityCannotFactorIndependence

reportMultiplicityStillCannotFactorIndependence :
  INF.FactorsThrough Testimony.countSurface Testimony.independenceStatus → ⊥
reportMultiplicityStillCannotFactorIndependence =
  Testimony.reportMultiplicityCannotFactorIndependence

------------------------------------------------------------------------
-- New regression 1: dependence status cannot determine evidential contribution.
-- Two dependent sources can differ in whether the second source adds useful
-- information or is effectively redundant.
------------------------------------------------------------------------

data DependencyCase : Set where
  dependentButInformative dependentAndRedundant : DependencyCase

data DependencySurface : Set where sourceDependencePresent : DependencySurface
data InformationContribution : Set where incrementalInformation redundantInformation : InformationContribution

dependencySurface : DependencyCase → DependencySurface
dependencySurface _ = sourceDependencePresent

informationContribution : DependencyCase → InformationContribution
informationContribution dependentButInformative = incrementalInformation
informationContribution dependentAndRedundant = redundantInformation

dependencyValueDefect : INF.NonFactorabilityWitness dependencySurface informationContribution
dependencyValueDefect = INF.nonFactorabilityWitness
  dependentButInformative dependentAndRedundant refl (λ ())

dependencyStatusCannotFactorInformationContribution :
  INF.FactorsThrough dependencySurface informationContribution → ⊥
dependencyStatusCannotFactorInformationContribution =
  INF.witnessRulesOutEveryFlatFactorisation dependencyValueDefect

------------------------------------------------------------------------
-- New regression 2: independence cannot determine source quality/reliability.
------------------------------------------------------------------------

data IndependenceQualityCase : Set where
  independentHighQuality independentLowQuality : IndependenceQualityCase

data IndependenceSurface : Set where sourceIndependencePresent : IndependenceSurface
data EvidenceQuality : Set where comparativelyHighQuality comparativelyLowQuality : EvidenceQuality

independenceSurface : IndependenceQualityCase → IndependenceSurface
independenceSurface _ = sourceIndependencePresent

evidenceQuality : IndependenceQualityCase → EvidenceQuality
evidenceQuality independentHighQuality = comparativelyHighQuality
evidenceQuality independentLowQuality = comparativelyLowQuality

independenceQualityDefect : INF.NonFactorabilityWitness independenceSurface evidenceQuality
independenceQualityDefect = INF.nonFactorabilityWitness
  independentHighQuality independentLowQuality refl (λ ())

independenceCannotFactorEvidenceQuality :
  INF.FactorsThrough independenceSurface evidenceQuality → ⊥
independenceCannotFactorEvidenceQuality =
  INF.witnessRulesOutEveryFlatFactorisation independenceQualityDefect

------------------------------------------------------------------------
-- New regression 3: agreement/consensus cannot recover provenance diversity.
-- The same apparent agreement can arise from independent convergence or from
-- information propagating through a common source/network route.
------------------------------------------------------------------------

data AgreementCase : Set where
  sameAgreementIndependentConvergence sameAgreementCommonRoute : AgreementCase

data AgreementSurface : Set where sameAgreement : AgreementSurface
data SourceDiversity : Set where provenanceDiverse provenanceConcentrated : SourceDiversity

agreementSurface : AgreementCase → AgreementSurface
agreementSurface _ = sameAgreement

sourceDiversity : AgreementCase → SourceDiversity
sourceDiversity sameAgreementIndependentConvergence = provenanceDiverse
sourceDiversity sameAgreementCommonRoute = provenanceConcentrated

agreementDiversityDefect : INF.NonFactorabilityWitness agreementSurface sourceDiversity
agreementDiversityDefect = INF.nonFactorabilityWitness
  sameAgreementIndependentConvergence sameAgreementCommonRoute refl (λ ())

agreementCannotFactorProvenanceDiversity :
  INF.FactorsThrough agreementSurface sourceDiversity → ⊥
agreementCannotFactorProvenanceDiversity =
  INF.witnessRulesOutEveryFlatFactorisation agreementDiversityDefect

------------------------------------------------------------------------
-- Cross-lane Snowball constraints.
------------------------------------------------------------------------

record DependencyReverseConstraint : Set where
  constructor dependency-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open DependencyReverseConstraint public

evidenceConstraint : DependencyReverseConstraint
evidenceConstraint = dependency-reverse-constraint
  "Evidence / corroboration"
  "multiplicity, dependence topology, source reliability, relevance, incremental information and proposition truth remain distinct"
  false

replicationConstraint : DependencyReverseConstraint
replicationConstraint = dependency-reverse-constraint
  "Replication / reproducibility"
  "same method, shared device, shared dataset, shared code, shared training lineage and independent reproduction are separately recoverable"
  false

mediaOsintConstraint : DependencyReverseConstraint
mediaOsintConstraint = dependency-reverse-constraint
  "Media / OSINT / AI retrieval"
  "many stories, posts or summaries may descend from one wire report, document, model output or retrieval source; surface multiplicity cannot erase source genealogy"
  false

socialInfluenceConstraint : DependencyReverseConstraint
socialInfluenceConstraint = dependency-reverse-constraint
  "Social influence / testimony"
  "agreement, communication path, common-source exposure, private judgment and consent/endorsement remain distinct"
  false

consensusConstraint : DependencyReverseConstraint
consensusConstraint = dependency-reverse-constraint
  "Scientific consensus"
  "agreement level, provenance diversity, methodological diversity, common training/model assumptions, uncertainty and proposition truth remain distinct"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data DependentEvidenceMeansWorthless : Set where
data IndependentEvidenceMeansReliable : Set where
data CommonSourceMeansFalse : Set where
data AgreementMeansIndependentSupport : Set where
data ConsensusMeansProvenanceDiverse : Set where
data DependencyQidCreatesDependencyReceipt : Set where

dependentEvidenceDoesNotMeanWorthless : DependentEvidenceMeansWorthless → ⊥
dependentEvidenceDoesNotMeanWorthless ()

independentEvidenceDoesNotMeanReliable : IndependentEvidenceMeansReliable → ⊥
independentEvidenceDoesNotMeanReliable ()

commonSourceDoesNotMeanFalse : CommonSourceMeansFalse → ⊥
commonSourceDoesNotMeanFalse ()

agreementDoesNotMeanIndependentSupport : AgreementMeansIndependentSupport → ⊥
agreementDoesNotMeanIndependentSupport ()

consensusDoesNotMeanProvenanceDiverse : ConsensusMeansProvenanceDiverse → ⊥
consensusDoesNotMeanProvenanceDiverse ()

dependencyQidWouldNotCreateDependencyReceipt : DependencyQidCreatesDependencyReceipt → ⊥
dependencyQidWouldNotCreateDependencyReceipt ()

record EvidenceDependencyInformationDiversityBoundary : Set where
  constructor evidence-dependency-information-diversity-boundary
  field
    primaryVersionOfRecordDoiRetained : Bool
    preprintIdentityRetainedSeparately : Bool
    exactDependencyQidLeftUnresolved : Bool
    exactDependencyDeweyLeftUnresolved : Bool
    priorMultiplicityIndependenceTheoremReused : Bool
    dependencySeparatedFromWorthlessness : Bool
    independenceSeparatedFromReliability : Bool
    agreementSeparatedFromProvenanceDiversity : Bool
    commonSourceSeparatedFromFalsity : Bool
    mediaOsintSourceGenealogyPropagated : Bool
    socialNetworkCommunicationDependencyPropagated : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open EvidenceDependencyInformationDiversityBoundary public

canonicalEvidenceDependencyInformationDiversityBoundary :
  EvidenceDependencyInformationDiversityBoundary
canonicalEvidenceDependencyInformationDiversityBoundary =
  evidence-dependency-information-diversity-boundary
    true true true true true true true true true true true true false
