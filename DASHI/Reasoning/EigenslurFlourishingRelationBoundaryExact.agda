module DASHI.Reasoning.EigenslurFlourishingRelationBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Governance.CapabilityFunctioningNonDescentExact as Capability
import DASHI.Reasoning.StructuralMetaphorTaskCompressionExact as Compression
import DASHI.Reasoning.RelationRepresentationAdequacyExact as Adequacy
import DASHI.Reasoning.RelationRepresentationRealizationExact as Realization
import DASHI.Reasoning.RelationRepresentationSourceRegistryExact as Sources

------------------------------------------------------------------------
-- EIGENSLUR / FLOURISHING ADAPTER
--
-- This is deliberately a thin domain adapter over the generic relation-
-- representation machinery.  It does not define virtue, contempt, flourishing,
-- or social meaning by fiat.  It records the exact experimental seam:
--
--   matched/situated pair
--   -> candidate relation code / transformation family
--   -> declared consumer tests
--   -> future-safe tests where dynamics matter
--   -> explicit target-domain realization obligation.
------------------------------------------------------------------------

data RelationExperiment : Set where
  eigenslurResidualExperiment
  flourishingImprovementExperiment
  : RelationExperiment

data PairRole : Set where
  markedMember baselineMember : PairRole

record SituatedContrastPair : Set where
  constructor situatedContrastPair
  field
    experiment : RelationExperiment
    situation : String
    marked : String
    baseline : String
    pairingJustification : String

open SituatedContrastPair public

------------------------------------------------------------------------
-- Candidate families remain plural.  No experiment is forced into a fixed
-- translation merely because the motivating vocabulary says eigen/direction.
------------------------------------------------------------------------

fixedDirectionCandidate : Adequacy.TransformationFamily
fixedDirectionCandidate = Adequacy.fixedTranslation

rotationCandidate : Adequacy.TransformationFamily
rotationCandidate = Adequacy.linearRotation

affineCandidate : Adequacy.TransformationFamily
affineCandidate = Adequacy.affineTransformation

nonlinearCandidate : Adequacy.TransformationFamily
nonlinearCandidate = Adequacy.learnedNonlinearTransformation

manifoldCandidate : Adequacy.TransformationFamily
manifoldCandidate = Adequacy.manifoldConstrainedTransformation

cosineCandidateGeometry : Adequacy.ComparisonGeometry
cosineCandidateGeometry = Adequacy.cosineLikeGeometry

ordinalCandidateGeometry : Adequacy.ComparisonGeometry
ordinalCandidateGeometry = Adequacy.ordinalConcordanceGeometry

geodesicCandidateGeometry : Adequacy.ComparisonGeometry
geodesicCandidateGeometry = Adequacy.riemannianGeodesicGeometry

------------------------------------------------------------------------
-- Matched-pair examples.  These are experimental schemas, not empirical rows.
------------------------------------------------------------------------

slurPairSchema : SituatedContrastPair
slurPairSchema =
  situatedContrastPair
    eigenslurResidualExperiment
    "one declared target/context with target identity held fixed"
    "contextualized derogatory epithet representation"
    "matched target-identity representation"
    "The subtraction/comparison is admissible only after the experimenter declares why the two representations are a matched pair."

virtuePairSchema : SituatedContrastPair
virtuePairSchema =
  situatedContrastPair
    flourishingImprovementExperiment
    "one declared ethical situation with contextual coordinates held fixed"
    "candidate virtuous/improved action-state representation"
    "matched neutral or baseline action-state representation"
    "The baseline is a matched counterfactual inside the same declared situation, not an unrelated word or circumstance label."

------------------------------------------------------------------------
-- A compact semantic relation can remain insufficient for situated meaning.
-- Reuse the generic realization collision rather than adding another descent
-- theorem.
------------------------------------------------------------------------

compactSemanticCodeDoesNotRealizeSituatedMeaning :
  Realization.RepresentationRealizationWitness
    Realization.compactRelation Realization.situatedMeaning → ⊥
compactSemanticCodeDoesNotRealizeSituatedMeaning =
  Realization.compactRelationCannotRealizeSituatedMeaning

------------------------------------------------------------------------
-- Flourishing cannot be reduced to realized functioning alone when capability
-- is a declared consumer.  This is exactly the existing Sen-calibrated DASHI
-- non-descent theorem, not a new ethics-specific proof.
------------------------------------------------------------------------

functioningDoesNotRecoverCapability :
  NonFactor.FactorsThrough
    Capability.functioning Capability.capabilitySignature → ⊥
functioningDoesNotRecoverCapability =
  Capability.functioningCannotRecoverCapability

capabilityDoesNotRecoverFunctioning :
  NonFactor.FactorsThrough
    Capability.capabilitySignature Capability.functioning → ⊥
capabilityDoesNotRecoverFunctioning =
  Capability.capabilityCannotRecoverFunctioning

------------------------------------------------------------------------
-- A synthetic rank-one-looking code can fit a coarse valence consumer and fail
-- a richer situated consumer.  Rank terminology here is only suggestive: no
-- matrix/SVD theorem is being claimed by this finite witness.
------------------------------------------------------------------------

data EthicalFineState : Set where
  helpfulWithChoice helpfulUnderCoercion : EthicalFineState

data CoarsePositiveCode : Set where positiveCode : CoarsePositiveCode

data CoarseValence : Set where positiveValence : CoarseValence

data AgencyStatus : Set where agencyPreserved agencyConstrained : AgencyStatus

data ValenceTask : Set where valenceTask : ValenceTask

coarsePositiveCode : EthicalFineState → CoarsePositiveCode
coarsePositiveCode _ = positiveCode

coarseValence : ValenceTask → EthicalFineState → CoarseValence
coarseValence _ _ = positiveValence

coarseValenceDecoder : ValenceTask → CoarsePositiveCode → CoarseValence
coarseValenceDecoder _ _ = positiveValence

agencyStatus : EthicalFineState → AgencyStatus
agencyStatus helpfulWithChoice = agencyPreserved
agencyStatus helpfulUnderCoercion = agencyConstrained

coarsePositiveCodeFitsValence :
  Compression.TaskRelativeStructuralCompression
    EthicalFineState CoarsePositiveCode ValenceTask CoarseValence
    coarsePositiveCode coarseValence
coarsePositiveCodeFitsValence =
  Compression.taskRelativeStructuralCompression
    coarseValenceDecoder
    (λ { valenceTask helpfulWithChoice → refl
       ; valenceTask helpfulUnderCoercion → refl
       })
    "The compact positive code is exactly sufficient for the deliberately coarse valence task."

coarsePositiveCodeLosesAgency :
  Compression.CompressionFailureWitness coarsePositiveCode agencyStatus
coarsePositiveCodeLosesAgency =
  Compression.compressionFailureWitness
    helpfulWithChoice
    helpfulUnderCoercion
    refl
    (λ ())

coarsePositiveCodeCannotRealizeAgency :
  Realization.RepresentationRealizationWitness coarsePositiveCode agencyStatus → ⊥
coarsePositiveCodeCannotRealizeAgency =
  Realization.representationCollisionBlocksRealization
    coarsePositiveCodeLosesAgency

------------------------------------------------------------------------
-- Source-facing claim boundary.
------------------------------------------------------------------------

record EigenslurFlourishingBoundary : Set where
  constructor eigenslurFlourishingBoundary
  field
    eigenslurRequiresFixedTranslation : Bool
    eigenslurRequiresFixedTranslationIsFalse :
      eigenslurRequiresFixedTranslation ≡ false

    flourishingRequiresRankOneDirection : Bool
    flourishingRequiresRankOneDirectionIsFalse :
      flourishingRequiresRankOneDirection ≡ false

    bestEmbeddingMetricDefinesVirtue : Bool
    bestEmbeddingMetricDefinesVirtueIsFalse :
      bestEmbeddingMetricDefinesVirtue ≡ false

    lowRankFitImpliesSemanticEssence : Bool
    lowRankFitImpliesSemanticEssenceIsFalse :
      lowRankFitImpliesSemanticEssence ≡ false

    transferableRelationCodeImpliesSituatedMeaning : Bool
    transferableRelationCodeImpliesSituatedMeaningIsFalse :
      transferableRelationCodeImpliesSituatedMeaning ≡ false

    realizedPositiveOutcomeImpliesCapabilityPreserved : Bool
    realizedPositiveOutcomeImpliesCapabilityPreservedIsFalse :
      realizedPositiveOutcomeImpliesCapabilityPreserved ≡ false

    representationFitImpliesNormativeAuthority : Bool
    representationFitImpliesNormativeAuthorityIsFalse :
      representationFitImpliesNormativeAuthority ≡ false

    matchedPairingMustBeDeclared : Bool
    matchedPairingMustBeDeclaredIsTrue :
      matchedPairingMustBeDeclared ≡ true

canonicalEigenslurFlourishingBoundary : EigenslurFlourishingBoundary
canonicalEigenslurFlourishingBoundary =
  eigenslurFlourishingBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl

sourceBoundary : Sources.RelationRepresentationAttributionBoundary
sourceBoundary = Sources.canonicalRelationRepresentationAttributionBoundary
