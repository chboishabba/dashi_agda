module DASHI.Wikimedia.IbrahimSnowballDependencyNDimLocalGlobalProofSearchBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.ExperimentalCoordinateDesignExact as Experiment
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Core.ArgumentResponseNonGeometricOppositeBidiExact as ArgumentGeometry
import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as EvidenceDesign
import DASHI.Topology.ClopenNDimFibreBoundary as ClopenNDim
import DASHI.Biology.SelfIndexedParetoHyperfabricTetrationExact as Tetration
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballLearningMemoryTraumaReplicationConsensusBidiExact as Prior
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey

------------------------------------------------------------------------
-- IBRAHIM / SNOWBALL DEPENDENCY + NDIM + LOCAL/GLOBAL BIDI
--
-- Repetition is first quotiented by provenance/dependency structure, but
-- dependency is not a Boolean "worthless" flag.  Partial dependence remains a
-- first-class evidential coordinate.  Local validity does not automatically
-- promote to global validity; a failed argument transport is not the logical or
-- geometric opposite of its conclusion; and NDim refinement is useful only
-- when a discriminator separates a live collision or improves admissible
-- compatibility/gluing for an exact consumer.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim dependency/NDim/local-global/proof-search BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "identity only; does not create independence, global validity, proof authority, causal force or consensus truth")

reproducibilityQid : Identity.ExternalIdentityDemand
reproducibilityQid = Prior.reproducibilityQid

scientificConsensusQid : Identity.ExternalIdentityDemand
scientificConsensusQid = Prior.scientificConsensusQid

learningQid : Identity.ExternalIdentityDemand
learningQid = Prior.learningQid

evidentialDependenceQid : Identity.ExternalIdentityDemand
evidentialDependenceQid = Identity.mkOptionalIdentityDemand
  "Ibrahim dependency/NDim/local-global/proof-search BIDI"
  "external concept identity"
  "evidential/source dependence"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact single QID promoted for evidential dependence/common-source dependence; retain as a typed provenance relation rather than forcing a nearby concept")

localGlobalValidityQid : Identity.ExternalIdentityDemand
localGlobalValidityQid = Identity.mkOptionalIdentityDemand
  "Ibrahim dependency/NDim/local-global/proof-search BIDI"
  "external concept identity"
  "local-to-global validity / transportability"
  Identity.wikidataQid
  (Identity.unresolved
    "no one exact cross-domain QID promoted; mathematical gluing, experimental transportability and legal scope remain distinct")

------------------------------------------------------------------------
-- Dewey remains navigation only.
------------------------------------------------------------------------

dependencyDewey : Dewey.DeweyCoordinate
dependencyDewey = Dewey.mkUnresolvedDewey
  "evidential dependence / common-source dependence"
  "no exact inspected DDC value promoted"

localGlobalDewey : Dewey.DeweyCoordinate
localGlobalDewey = Dewey.mkUnresolvedDewey
  "local-to-global inference / transportability"
  "cross-domain concept retained without forcing one library shelf"

------------------------------------------------------------------------
-- DOI/source payment for the dependency seam.
------------------------------------------------------------------------

pilditchDependency2025 : Attribution.AttributedSource
pilditchDependency2025 = Attribution.mkDOISource
  "Toby D. Pilditch; Ulrike Hahn; David Lagnado"
  "The problem of dependency"
  "Synthese 205, 143"
  "2025"
  "10.1007/s11229-025-04969-w"
  "https://doi.org/10.1007/s11229-025-04969-w"
  Attribution.academicArticleSource
  "formal/epistemic analysis of non-independence across evidence and testimony; dependency can create redundancy and overconfidence, but real dependency structures are richer than a binary independent/worthless classification"
  Attribution.publicAttribution

pilditchDependency2020 : Attribution.AttributedSource
pilditchDependency2020 = Attribution.mkDOISource
  "Toby D. Pilditch; Ulrike Hahn; Norman Fenton; David Lagnado"
  "Dependencies in evidential reports: The case for informational advantages"
  "Cognition 204, 104343"
  "2020"
  "10.1016/j.cognition.2020.104343"
  "https://doi.org/10.1016/j.cognition.2020.104343"
  Attribution.academicArticleSource
  "distinguishes dependency-network structure from observations and shows that some dependent structures can carry informational advantages; does not imply dependence is always beneficial"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Dependency topology is richer than independent/dependent Boolean collapse.
------------------------------------------------------------------------

data DependencyGrade : Set where
  independent : DependencyGrade
  partiallyDependent : DependencyGrade
  sharedEvidenceDependent : DependencyGrade
  copiedOrCommonSource : DependencyGrade

data EvidenceMultiplicityCase : Set where
  sameCountIndependent sameCountPartial sameCountCommonSource : EvidenceMultiplicityCase

data CountSurface : Set where sameEvidenceCount : CountSurface

countSurface : EvidenceMultiplicityCase → CountSurface
countSurface _ = sameEvidenceCount

dependencyGrade : EvidenceMultiplicityCase → DependencyGrade
dependencyGrade sameCountIndependent = independent
dependencyGrade sameCountPartial = partiallyDependent
dependencyGrade sameCountCommonSource = copiedOrCommonSource

countDependencyDefect : INF.NonFactorabilityWitness countSurface dependencyGrade
countDependencyDefect = INF.nonFactorabilityWitness
  sameCountIndependent sameCountPartial refl (λ ())

multiplicityCannotFactorDependencyTopology :
  INF.FactorsThrough countSurface dependencyGrade → ⊥
multiplicityCannotFactorDependencyTopology =
  INF.witnessRulesOutEveryFlatFactorisation countDependencyDefect

------------------------------------------------------------------------
-- Partial dependence is retained rather than mapped to zero information.
------------------------------------------------------------------------

data EvidentialValue : Set where
  noAdditionalInformation : EvidentialValue
  partialAdditionalInformation : EvidentialValue
  distinctAdditionalInformation : EvidentialValue

dependencyMayRetainInformation : DependencyGrade → EvidentialValue
 dependencyMayRetainInformation independent = distinctAdditionalInformation
 dependencyMayRetainInformation partiallyDependent = partialAdditionalInformation
 dependencyMayRetainInformation sharedEvidenceDependent = partialAdditionalInformation
 dependencyMayRetainInformation copiedOrCommonSource = noAdditionalInformation

------------------------------------------------------------------------
-- TRUE(HERE) != TRUE(EVERYWHERE): scope/transport is a separate consumer.
------------------------------------------------------------------------

data ScopeCase : Set where
  sameLocalResultTransports sameLocalResultDoesNotTransport : ScopeCase

data LocalResultSurface : Set where sameTrueHereSurface : LocalResultSurface
data TransportStatus : Set where transportPaid transportOpenOrFails : TransportStatus

localResultSurface : ScopeCase → LocalResultSurface
localResultSurface _ = sameTrueHereSurface

transportStatus : ScopeCase → TransportStatus
transportStatus sameLocalResultTransports = transportPaid
transportStatus sameLocalResultDoesNotTransport = transportOpenOrFails

localGlobalDefect : INF.NonFactorabilityWitness localResultSurface transportStatus
localGlobalDefect = INF.nonFactorabilityWitness
  sameLocalResultTransports sameLocalResultDoesNotTransport refl (λ ())

trueHereCannotFactorTrueEverywhere :
  INF.FactorsThrough localResultSurface transportStatus → ⊥
trueHereCannotFactorTrueEverywhere =
  INF.witnessRulesOutEveryFlatFactorisation localGlobalDefect

------------------------------------------------------------------------
-- A failed route or fallacy obstructs transport; it is not the geometric
-- antipode or automatic refutation of the target.
------------------------------------------------------------------------

argumentGeometryBoundary : ArgumentGeometry.ArgumentResponseGeometryBoundary
argumentGeometryBoundary = ArgumentGeometry.canonicalArgumentResponseGeometryBoundary

evidenceDesignBoundary : EvidenceDesign.EvidenceDesignBoundary
evidenceDesignBoundary = EvidenceDesign.canonicalEvidenceDesignBoundary

proofSearchBoundary : ProofSearch.ProofSearchLeastPrivilegeBoundary
proofSearchBoundary = ProofSearch.canonicalProofSearchLeastPrivilegeBoundary

experimentalCoordinateBoundary : Experiment.ExperimentalCoordinateBoundary
experimentalCoordinateBoundary = Experiment.canonicalExperimentalCoordinateBoundary

------------------------------------------------------------------------
-- NDim / Hyperfabric / p-adic / pants geometry: dimensions may refine local
-- observational resolution; that does not promote arbitrary global gluing.
------------------------------------------------------------------------

clopenNDimBoundary : ClopenNDim.ClopenNDimBoundary
clopenNDimBoundary = ClopenNDim.canonicalClopenNDimBoundary

tetrationBoundary : Tetration.SelfIndexedParetoTetrationBoundary
tetrationBoundary = Tetration.canonicalSelfIndexedParetoTetrationBoundary

data RefinementCase : Set where
  addedAxisSeparatesCollision addedAxisDoesNotSeparateCollision : RefinementCase

data AxisCountSurface : Set where sameAddedDimensionCount : AxisCountSurface
data UsefulRefinement : Set where usefulForConsumer noUsefulReduction : UsefulRefinement

axisCountSurface : RefinementCase → AxisCountSurface
axisCountSurface _ = sameAddedDimensionCount

usefulRefinement : RefinementCase → UsefulRefinement
usefulRefinement addedAxisSeparatesCollision = usefulForConsumer
usefulRefinement addedAxisDoesNotSeparateCollision = noUsefulReduction

refinementUtilityDefect : INF.NonFactorabilityWitness axisCountSurface usefulRefinement
refinementUtilityDefect = INF.nonFactorabilityWitness
  addedAxisSeparatesCollision addedAxisDoesNotSeparateCollision refl (λ ())

moreDimensionsCannotFactorUsefulReduction :
  INF.FactorsThrough axisCountSurface usefulRefinement → ⊥
moreDimensionsCannotFactorUsefulReduction =
  INF.witnessRulesOutEveryFlatFactorisation refinementUtilityDefect

------------------------------------------------------------------------
-- Compatibility/gluing must be paid separately from local validity.
------------------------------------------------------------------------

data LocalFamilyCase : Set where
  sameLocalValidityCompatibleFamily sameLocalValidityConflictingFamily : LocalFamilyCase

data LocalValiditySurface : Set where sameLocallyValidCandidates : LocalValiditySurface
data GlobalCompatibility : Set where compatibleForGluing conflictRemains : GlobalCompatibility

localValiditySurface : LocalFamilyCase → LocalValiditySurface
localValiditySurface _ = sameLocallyValidCandidates

globalCompatibility : LocalFamilyCase → GlobalCompatibility
globalCompatibility sameLocalValidityCompatibleFamily = compatibleForGluing
globalCompatibility sameLocalValidityConflictingFamily = conflictRemains

localCompatibilityDefect : INF.NonFactorabilityWitness localValiditySurface globalCompatibility
localCompatibilityDefect = INF.nonFactorabilityWitness
  sameLocalValidityCompatibleFamily sameLocalValidityConflictingFamily refl (λ ())

localValidityCannotFactorGlobalCompatibility :
  INF.FactorsThrough localValiditySurface globalCompatibility → ⊥
localValidityCannotFactorGlobalCompatibility =
  INF.witnessRulesOutEveryFlatFactorisation localCompatibilityDefect

------------------------------------------------------------------------
-- Reverse BIDI constraints into Ibrahim parents.
------------------------------------------------------------------------

record DependencyNDimReverseConstraint : Set where
  constructor dependency-ndim-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open DependencyNDimReverseConstraint public

evidenceConstraint : DependencyNDimReverseConstraint
evidenceConstraint = dependency-ndim-reverse-constraint
  "Evidence / corroboration"
  "count, provenance graph, partial dependence, copied/common-source dependence, reliability and evidential contribution remain separate"
  false

experimentConstraint : DependencyNDimReverseConstraint
experimentConstraint = dependency-ndim-reverse-constraint
  "Experiment / study design"
  "internal validity, external validity, sampling frame, comparator, nuisance coordinates, derived discriminators and transport domain remain separate"
  false

proofSearchConstraint : DependencyNDimReverseConstraint
proofSearchConstraint = dependency-ndim-reverse-constraint
  "Proof search / reasoning"
  "local lemma, route admission, exact consumer, obstruction/fallacy, alternative explanation and programme progress remain separate"
  false

geometryConstraint : DependencyNDimReverseConstraint
geometryConstraint = dependency-ndim-reverse-constraint
  "NDim / fibre / hyperfabric / p-adic / pants gluing"
  "local fibre refinement, coordinate utility, boundary restriction, seam compatibility and global gluing remain separately witnessed"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data DependenceMeansWorthless : Set where
data CountMeansIndependence : Set where
data TrueHereMeansTrueEverywhere : Set where
data FallacyMeansConclusionFalse : Set where
data AdversarialResponseMeansGeometricOpposite : Set where
data MoreDimensionsMeanMoreKnowledge : Set where
data LocalValidityMeansGlobalAdmissibility : Set where
data TetrationalGrowthMeansSemanticCompleteness : Set where

dependenceDoesNotMeanWorthless : DependenceMeansWorthless → ⊥
dependenceDoesNotMeanWorthless ()

countDoesNotMeanIndependence : CountMeansIndependence → ⊥
countDoesNotMeanIndependence ()

trueHereDoesNotMeanTrueEverywhere : TrueHereMeansTrueEverywhere → ⊥
trueHereDoesNotMeanTrueEverywhere ()

fallacyDoesNotMeanConclusionFalse : FallacyMeansConclusionFalse → ⊥
fallacyDoesNotMeanConclusionFalse ()

adversarialResponseDoesNotMeanGeometricOpposite : AdversarialResponseMeansGeometricOpposite → ⊥
adversarialResponseDoesNotMeanGeometricOpposite ()

moreDimensionsDoNotMeanMoreKnowledge : MoreDimensionsMeanMoreKnowledge → ⊥
moreDimensionsDoNotMeanMoreKnowledge ()

localValidityDoesNotMeanGlobalAdmissibility : LocalValidityMeansGlobalAdmissibility → ⊥
localValidityDoesNotMeanGlobalAdmissibility ()

tetrationalGrowthDoesNotMeanSemanticCompleteness : TetrationalGrowthMeansSemanticCompleteness → ⊥
tetrationalGrowthDoesNotMeanSemanticCompleteness ()

record DependencyNDimLocalGlobalProofSearchBoundary : Set where
  constructor dependency-ndim-local-global-proof-search-boundary
  field
    qidsAttachedOrExplicitlyUnresolved : Bool
    deweyUnresolvedStateRetained : Bool
    pilditchDependencySourcesAttached : Bool
    partialDependenceRetained : Bool
    multiplicitySeparatedFromIndependence : Bool
    trueHereSeparatedFromTrueEverywhere : Bool
    fallacySeparatedFromConclusionTruth : Bool
    responseSeparatedFromGeometricOpposite : Bool
    addedAxisRequiresDiscriminatoryUtility : Bool
    localValiditySeparatedFromGlobalGluing : Bool
    proofSearchLeastPrivilegeReused : Bool
    tetrationAndPadicGeometryNotSemanticPromotion : Bool
    presentAxisVocabularyClaimedComplete : Bool
open DependencyNDimLocalGlobalProofSearchBoundary public

canonicalDependencyNDimLocalGlobalProofSearchBoundary :
  DependencyNDimLocalGlobalProofSearchBoundary
canonicalDependencyNDimLocalGlobalProofSearchBoundary =
  dependency-ndim-local-global-proof-search-boundary
    true true true true true true true true true true true true false
