module DASHI.Reasoning.ImplementationExperimentProvenanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- IMPLEMENTATION / MIRROR / EXPERIMENT / FORMALIZATION PROVENANCE
--
-- Cross-pollination motivation:
--   * #625 / situated-authority work keeps provenance, permission, empirical
--     adequacy and downstream authority separately typed;
--   * the DASHIg / Leech audit exposed the software analogue: repository
--     location, implementation authorship, experiment ownership and formal
--     theorem ownership are distinct coordinates.
--
-- This module is a DASHI provenance construction. It does not attribute the
-- generic separation theorem to any external source.
------------------------------------------------------------------------

data ProvenanceRole : Set where
  primaryImplementationSource
  mirrorOrCloneLocation
  experimentProducer
  dataOrArtifactProducer
  formalizationOwner
  downstreamInferenceOwner
  : ProvenanceRole

record ProvenanceCoordinate : Set where
  constructor provenanceCoordinate
  field
    role : ProvenanceRole
    identifier : String
    reading : String

open ProvenanceCoordinate public

record ImplementationExperimentProvenance : Set where
  constructor implementationExperimentProvenance
  field
    implementationSource : ProvenanceCoordinate
    accessLocation : ProvenanceCoordinate
    experimentSource : ProvenanceCoordinate
    artifactSource : ProvenanceCoordinate
    formalSource : ProvenanceCoordinate
    inferenceSource : ProvenanceCoordinate

open ImplementationExperimentProvenance public

------------------------------------------------------------------------
-- Permission to use one coordinate does not collapse the others.
------------------------------------------------------------------------

record ProvenanceNonPromotionBoundary : Set where
  constructor provenanceNonPromotionBoundary
  field
    mirrorOwnershipImpliesImplementationAuthorship : Bool
    mirrorOwnershipImpliesImplementationAuthorshipIsFalse :
      mirrorOwnershipImpliesImplementationAuthorship ≡ false

    experimentOwnershipImpliesImplementationAuthorship : Bool
    experimentOwnershipImpliesImplementationAuthorshipIsFalse :
      experimentOwnershipImpliesImplementationAuthorship ≡ false

    formalizationOwnershipImpliesEmpiricalAuthorship : Bool
    formalizationOwnershipImpliesEmpiricalAuthorshipIsFalse :
      formalizationOwnershipImpliesEmpiricalAuthorship ≡ false

    sourceCitationTransfersTheoremAuthorship : Bool
    sourceCitationTransfersTheoremAuthorshipIsFalse :
      sourceCitationTransfersTheoremAuthorship ≡ false

    pinnedAccessLocationIsStillUsefulProvenance : Bool
    pinnedAccessLocationIsStillUsefulProvenanceIsTrue :
      pinnedAccessLocationIsStillUsefulProvenance ≡ true

canonicalProvenanceNonPromotionBoundary : ProvenanceNonPromotionBoundary
canonicalProvenanceNonPromotionBoundary =
  provenanceNonPromotionBoundary
    false refl
    false refl
    false refl
    false refl
    true refl

------------------------------------------------------------------------
-- Concrete finite Leech/DASHIg provenance specimen.
--
-- The implementation author coordinate is intentionally unresolved. The
-- secondary mirrored citation claim belongs in the experiment-specific module;
-- this generic specimen only records the known location/ownership separation.
------------------------------------------------------------------------

leechImplementationSource : ProvenanceCoordinate
leechImplementationSource =
  provenanceCoordinate
    primaryImplementationSource
    "SPUTNIKAI/LeechTransformer (historical submodule target; primary endpoint currently unresolved)"
    "Primary implementation provenance is not inferred from any mirror owner."

leechMirrorLocation : ProvenanceCoordinate
leechMirrorLocation =
  provenanceCoordinate
    mirrorOrCloneLocation
    "meta-introspector/LeechTransformer"
    "Known clone/mirror-like access surface; repository ownership is not treated as implementation authorship."

dashigExperimentProducer : ProvenanceCoordinate
dashigExperimentProducer =
  provenanceCoordinate
    experimentProducer
    "chboishabba/DASHIg@013962fb839e83ce8e4b35486fe1a79792c96db8"
    "Pinned Phase-2 grokking comparison experiment producer."

dashigArtifactProducer : ProvenanceCoordinate
dashigArtifactProducer =
  provenanceCoordinate
    dataOrArtifactProducer
    "DASHIg pinned CSV/trajectory artifacts"
    "Literal preliminary outputs of the pinned Phase-2 experiment surface."

dashiAgdaFormalizationOwner : ProvenanceCoordinate
dashiAgdaFormalizationOwner =
  provenanceCoordinate
    formalizationOwner
    "chboishabba/dashi_agda"
    "Owns the finite formal bridge and claim boundaries, not the upstream implementation."

toeInferenceOwner : ProvenanceCoordinate
toeInferenceOwner =
  provenanceCoordinate
    downstreamInferenceOwner
    "DASHI Stage-6/7 experiment architecture"
    "Owns prediction-envelope / calibrated-inference / robustness semantics after evidence admission."

canonicalLeechDASHIgProvenance : ImplementationExperimentProvenance
canonicalLeechDASHIgProvenance =
  implementationExperimentProvenance
    leechImplementationSource
    leechMirrorLocation
    dashigExperimentProducer
    dashigArtifactProducer
    dashiAgdaFormalizationOwner
    toeInferenceOwner
