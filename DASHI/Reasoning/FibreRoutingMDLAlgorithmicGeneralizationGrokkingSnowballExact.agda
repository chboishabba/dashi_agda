module DASHI.Reasoning.FibreRoutingMDLAlgorithmicGeneralizationGrokkingSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Reasoning.FibreRoutingCompressionIbrahimSnowballExact as Compression
import DASHI.Reasoning.FibreRoutingRateDistortionInformationBottleneckSnowballExact as RateIB

------------------------------------------------------------------------
-- IBRAHIM FOLLOW:
-- MDL -> Occam/parsimony -> algorithmic information/Kolmogorov complexity
-- -> learnability/generalization -> grokking.
--
-- Compression or short description may be evidence about representation
-- structure, but shortest is not automatically true, causal, robust, or safe
-- for a declared consumer.  Grokking is an empirical generalization phenomenon
-- and remains distinct from any proposed compression mechanism.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim MDL/algorithmic-information/generalization/grokking snowball"
  "verified external concept identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "identity checked 2026-09-11; QID does not create compression theorem, simplicity preference, generalization guarantee or grokking mechanism")

algorithmicInformationTheoryQid : Identity.ExternalIdentityDemand
algorithmicInformationTheoryQid = mkQid "algorithmic information theory" "Q1757543"

kolmogorovComplexityQid : Identity.ExternalIdentityDemand
kolmogorovComplexityQid = mkQid "Kolmogorov complexity" "Q1456811"

occamsRazorQid : Identity.ExternalIdentityDemand
occamsRazorQid = mkQid "Occam's razor" "Q131012"

minimumDescriptionLengthQid : Identity.ExternalIdentityDemand
minimumDescriptionLengthQid = Compression.minimumDescriptionLengthQid

grokkingQid : Identity.ExternalIdentityDemand
grokkingQid = Compression.grokkingQid

generalizationQid : Identity.ExternalIdentityDemand
generalizationQid = Identity.mkOptionalIdentityDemand
  "Ibrahim MDL/algorithmic-information/generalization/grokking snowball"
  "exact machine-learning concept identity"
  "generalization in machine learning"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact same-concept QID safely promoted in this pass; generic generalization relations/properties do not substitute")

pacLearnabilityQid : Identity.ExternalIdentityDemand
pacLearnabilityQid = Identity.mkOptionalIdentityDemand
  "Ibrahim MDL/algorithmic-information/generalization/grokking snowball"
  "exact concept identity"
  "probably approximately correct learning / computational learnability"
  Identity.wikidataQid
  (Identity.unresolved
    "Valiant primary source is retained by DOI/canonical link; no exact concept QID promoted here")

------------------------------------------------------------------------
-- Dewey navigation remains independently sourced.
------------------------------------------------------------------------

data AlgorithmicDeweyResolution : Set where
  deweyVerified : String → String → AlgorithmicDeweyResolution
  deweyUnresolved : String → AlgorithmicDeweyResolution

record AlgorithmicDeweyCoordinate : Set where
  constructor algorithmic-dewey-coordinate
  field
    subjectLabel : String
    resolution : AlgorithmicDeweyResolution
    classificationCreatesGeneralization : Bool
open AlgorithmicDeweyCoordinate public

algorithmicInformationDewey : AlgorithmicDeweyCoordinate
algorithmicInformationDewey = algorithmic-dewey-coordinate
  "algorithmic information theory"
  (deweyUnresolved "no exact inspected DDC statement promoted for Q1757543")
  false

kolmogorovComplexityDewey : AlgorithmicDeweyCoordinate
kolmogorovComplexityDewey = algorithmic-dewey-coordinate
  "Kolmogorov complexity"
  (deweyUnresolved "no exact inspected DDC statement promoted for Q1456811")
  false

occamDewey : AlgorithmicDeweyCoordinate
occamDewey = algorithmic-dewey-coordinate
  "Occam's razor"
  (deweyUnresolved "no exact inspected DDC statement promoted for Q131012")
  false

machineLearningDewey : Compression.CompressionDeweyCoordinate
machineLearningDewey = Compression.machineLearningDewey

------------------------------------------------------------------------
-- Primary/source-bounded lineage.  Canonical DOI links are part of attribution.
------------------------------------------------------------------------

solomonoffInductionSource : Attribution.AttributedSource
solomonoffInductionSource = Attribution.mkDOISource
  "Ray J. Solomonoff"
  "A Formal Theory of Inductive Inference. Part I"
  "Information and Control 7(1), 1-22"
  "1964"
  "10.1016/S0019-9958(64)90223-2"
  "https://doi.org/10.1016/S0019-9958(64)90223-2"
  Attribution.academicArticleSource
  "primary algorithmic-induction lineage using universal-machine description lengths as prior structure; does not imply that shortest DASHI carrier is causally or consumer-adequate"
  Attribution.publicAttribution

valiantLearnableSource : Attribution.AttributedSource
valiantLearnableSource = Attribution.mkDOISource
  "Leslie G. Valiant"
  "A Theory of the Learnable"
  "Communications of the ACM 27(11), 1134-1142"
  "1984"
  "10.1145/1968.1972"
  "https://doi.org/10.1145/1968.1972"
  Attribution.academicArticleSource
  "primary computational learnability/generalization framework; learnability under a specified protocol does not prove MDL optimality or grokking mechanism"
  Attribution.publicAttribution

rissanenMDLSource : Attribution.AttributedSource
rissanenMDLSource = Compression.rissanenMDLSource

powerGrokkingSource : Attribution.AttributedSource
powerGrokkingSource = Compression.powerGrokkingSource

------------------------------------------------------------------------
-- Regression 1: equal/short description length does not recover held-out
-- generalization for an arbitrary consumer.
------------------------------------------------------------------------

data DescriptionCase : Set where
  sameDescriptionCostGeneralizes sameDescriptionCostFailsHeldOut : DescriptionCase

data DescriptionSurface : Set where sameDescriptionLength : DescriptionSurface
data GeneralizationStatus : Set where heldOutConsumerPreserved heldOutConsumerFails : GeneralizationStatus

descriptionSurface : DescriptionCase → DescriptionSurface
descriptionSurface _ = sameDescriptionLength

generalizationStatus : DescriptionCase → GeneralizationStatus
generalizationStatus sameDescriptionCostGeneralizes = heldOutConsumerPreserved
generalizationStatus sameDescriptionCostFailsHeldOut = heldOutConsumerFails

descriptionGeneralizationDefect : INF.NonFactorabilityWitness descriptionSurface generalizationStatus
descriptionGeneralizationDefect = INF.nonFactorabilityWitness
  sameDescriptionCostGeneralizes sameDescriptionCostFailsHeldOut refl (λ ())

descriptionLengthCannotFactorHeldOutGeneralization :
  INF.FactorsThrough descriptionSurface generalizationStatus → ⊥
descriptionLengthCannotFactorHeldOutGeneralization =
  INF.witnessRulesOutEveryFlatFactorisation descriptionGeneralizationDefect

------------------------------------------------------------------------
-- Regression 2: same grokking/generalization onset need not determine the same
-- representation-compression mechanism.
------------------------------------------------------------------------

data GrokkingCase : Set where
  sameGrokkingOnsetCompressionMechanismA sameGrokkingOnsetCompressionMechanismB : GrokkingCase

data GrokkingSurface : Set where sameDelayedGeneralizationSurface : GrokkingSurface
data MechanismStatus : Set where compressionMechanismA compressionMechanismB : MechanismStatus

grokkingSurface : GrokkingCase → GrokkingSurface
grokkingSurface _ = sameDelayedGeneralizationSurface

mechanismStatus : GrokkingCase → MechanismStatus
mechanismStatus sameGrokkingOnsetCompressionMechanismA = compressionMechanismA
mechanismStatus sameGrokkingOnsetCompressionMechanismB = compressionMechanismB

grokkingMechanismDefect : INF.NonFactorabilityWitness grokkingSurface mechanismStatus
grokkingMechanismDefect = INF.nonFactorabilityWitness
  sameGrokkingOnsetCompressionMechanismA sameGrokkingOnsetCompressionMechanismB refl (λ ())

grokkingSurfaceCannotFactorCompressionMechanism :
  INF.FactorsThrough grokkingSurface mechanismStatus → ⊥
grokkingSurfaceCannotFactorCompressionMechanism =
  INF.witnessRulesOutEveryFlatFactorisation grokkingMechanismDefect

------------------------------------------------------------------------
-- Existing compression/information-theory boundaries reused.
------------------------------------------------------------------------

compressionBoundary : Compression.FibreCompressionIbrahimSnowballBoundary
compressionBoundary = Compression.canonicalFibreCompressionIbrahimSnowballBoundary

rateIBBoundary : RateIB.FibreRateDistortionInformationBottleneckBoundary
rateIBBoundary = RateIB.canonicalFibreRateDistortionInformationBottleneckBoundary

------------------------------------------------------------------------
-- Reverse Ibrahim constraints.
------------------------------------------------------------------------

record AlgorithmicReverseConstraint : Set where
  constructor algorithmic-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open AlgorithmicReverseConstraint public

mdlConstraint : AlgorithmicReverseConstraint
mdlConstraint = algorithmic-reverse-constraint
  "MDL / description length"
  "description cost, coding assumptions, model class, held-out consumer adequacy and mechanism truth remain distinct"
  false

algorithmicInformationConstraint : AlgorithmicReverseConstraint
algorithmicInformationConstraint = algorithmic-reverse-constraint
  "Algorithmic information / Kolmogorov complexity"
  "program-size complexity, universal-machine dependence up to invariance, predictive task and causal realization remain distinct consumers"
  false

occamConstraint : AlgorithmicReverseConstraint
occamConstraint = algorithmic-reverse-constraint
  "Occam / parsimony"
  "simplicity heuristic, formal description length, empirical generalization and truth remain distinct"
  false

generalizationConstraint : AlgorithmicReverseConstraint
generalizationConstraint = algorithmic-reverse-constraint
  "Learnability / generalization / grokking"
  "learning protocol, sample assumptions, held-out performance, delayed onset, representation cost and explanatory mechanism remain separate"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data ShortestDescriptionMeansTrue : Set where
data OccamMeansMDL : Set where
data PACLearnableMeansGrokking : Set where
data GrokkingMeansKolmogorovCompression : Set where
data QidCreatesMechanism : Set where
data CanonicalLinkCreatesPriority : Set where

shortestDescriptionDoesNotMeanTrue : ShortestDescriptionMeansTrue → ⊥
shortestDescriptionDoesNotMeanTrue ()

occamDoesNotMeanMDLIdentity : OccamMeansMDL → ⊥
occamDoesNotMeanMDLIdentity ()

pacLearnableDoesNotMeanGrokking : PACLearnableMeansGrokking → ⊥
pacLearnableDoesNotMeanGrokking ()

grokkingDoesNotMeanKolmogorovCompression : GrokkingMeansKolmogorovCompression → ⊥
grokkingDoesNotMeanKolmogorovCompression ()

qidDoesNotCreateMechanism : QidCreatesMechanism → ⊥
qidDoesNotCreateMechanism ()

canonicalLinkDoesNotCreateHistoricalPriority : CanonicalLinkCreatesPriority → ⊥
canonicalLinkDoesNotCreateHistoricalPriority ()

record FibreMDLAlgorithmicGeneralizationGrokkingBoundary : Set where
  constructor fibre-mdl-algorithmic-generalization-grokking-boundary
  field
    safeQidsAttached : Bool
    unresolvedQidsRetained : Bool
    canonicalLinksRetained : Bool
    doiOrPrimaryCanonicalIdentifierRetained : Bool
    primarySourceRolesExplicit : Bool
    deweyAttachedOnlyWhenInspected : Bool
    occamDistinctFromFormalMDL : Bool
    descriptionLengthSeparatedFromGeneralization : Bool
    generalizationSeparatedFromGrokkingMechanism : Bool
    shortestRepresentationSeparatedFromTruth : Bool
    presentAxisVocabularyClaimedComplete : Bool
open FibreMDLAlgorithmicGeneralizationGrokkingBoundary public

canonicalFibreMDLAlgorithmicGeneralizationGrokkingBoundary :
  FibreMDLAlgorithmicGeneralizationGrokkingBoundary
canonicalFibreMDLAlgorithmicGeneralizationGrokkingBoundary =
  fibre-mdl-algorithmic-generalization-grokking-boundary
    true true true true true true true true true true false
