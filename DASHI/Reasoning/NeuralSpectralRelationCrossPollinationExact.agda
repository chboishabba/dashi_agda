module DASHI.Reasoning.NeuralSpectralRelationCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Biology.NeuralRepresentationLaplacianExact as Neural
import DASHI.Biology.SpectralGrokkingLatticeExact as Spectral
import DASHI.Reasoning.StructuralMetaphorTaskCompressionExact as Compression
import DASHI.Reasoning.RelationRepresentationRealizationExact as Realization
import DASHI.Reasoning.RelationRepresentationExperimentProtocolExact as Protocol

------------------------------------------------------------------------
-- NEURAL / SPECTRAL CROSS-POLLINATION
--
-- Existing Biology owners already separate:
--
-- representation geometry
-- activation state
-- dynamics
-- Laplacian/relational variation
-- measurement
-- grokking phase / cleanup.
--
-- This module reuses those exact finite witnesses as a relation-representation
-- stress test.  It does not claim that the finite graph Laplacian is a literal
-- LLM activation manifold or that the grokking phase table is a universal
-- training law.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Same coarse measurement, different relational variation.
------------------------------------------------------------------------

coarseNeuralObservationCollision :
  Neural.fmriLikeObservation Neural.microActivationA
  ≡ Neural.fmriLikeObservation Neural.microActivationB
coarseNeuralObservationCollision = Neural.fmriProjectionCollision

neuralCoarseCompressionLosesVariation :
  Compression.CompressionFailureWitness
    Neural.fmriLikeObservation Neural.laplacianVariation
neuralCoarseCompressionLosesVariation =
  Compression.compressionFailureWitness
    Neural.microActivationA
    Neural.microActivationB
    Neural.fmriProjectionCollision
    (λ ())

neuralCoarseObservationCannotRealizeVariation :
  Realization.RepresentationRealizationWitness
    Neural.fmriLikeObservation Neural.laplacianVariation → ⊥
neuralCoarseObservationCannotRealizeVariation =
  Realization.representationCollisionBlocksRealization
    neuralCoarseCompressionLosesVariation

neuralCollisionRejectsCurrentCandidate :
  Protocol.CandidateConsumerFailure
    Neural.fmriLikeObservation Neural.laplacianVariation
neuralCollisionRejectsCurrentCandidate =
  Protocol.candidateConsumerFailure
    neuralCoarseCompressionLosesVariation
    Protocol.offsetCandidate
    "A coarse measurement can support some tasks while erasing relational/Laplacian variation; the rejected candidate is only the current coarse code, not neural representation in general."

neuralSearchMayReopenFromOffsetToRotation :
  Protocol.ReopenedCandidateSearch
    Neural.fmriLikeObservation Neural.laplacianVariation
neuralSearchMayReopenFromOffsetToRotation =
  Protocol.reopenedCandidateSearch
    neuralCollisionRejectsCurrentCandidate
    Protocol.rotationCandidate
    Protocol.offsetToRotation
    true refl
    "The collision licenses reopening into a richer candidate family while retaining the lost variation as a residual obligation."

------------------------------------------------------------------------
-- Grokking/spectral structure supplies a second independent lesson: cleanup can
-- remove irregular components while retaining symmetry-adapted modes.  This is
-- a representation-compression specimen, not proof that every learned semantic
-- relation is spectral or Fourier.
------------------------------------------------------------------------

cleanupEliminatesIrregularComponents :
  Spectral.irregularComponentCount Spectral.cleanupPhase ≡ 0
cleanupEliminatesIrregularComponents = Spectral.cleanupRemovesIrregularComponents

cleanupRetainsSymmetryAdaptedModes :
  Spectral.symmetryAdaptedComponentCount Spectral.cleanupPhase ≡ 3
cleanupRetainsSymmetryAdaptedModes = Spectral.cleanupRetainsThreeSymmetryModes

spectralContrastModesRemainDegenerate :
  Spectral.laplacianEigenvalue Spectral.cosineMode
  ≡ Spectral.laplacianEigenvalue Spectral.sineMode
spectralContrastModesRemainDegenerate = Spectral.contrastModesAreDegenerate

------------------------------------------------------------------------
-- Boundary: equal eigenvalue / retained mode count does not identify complete
-- representation, phase, semantics, or future behavior.
------------------------------------------------------------------------

record NeuralSpectralRelationBoundary : Set where
  constructor neuralSpectralRelationBoundary
  field
    coarseMeasurementDeterminesRelationalVariation : Bool
    coarseMeasurementDeterminesRelationalVariationIsFalse :
      coarseMeasurementDeterminesRelationalVariation ≡ false

    equalSpectralEigenvalueIdentifiesMode : Bool
    equalSpectralEigenvalueIdentifiesModeIsFalse :
      equalSpectralEigenvalueIdentifiesMode ≡ false

    cleanupModeCountDeterminesSemanticRelation : Bool
    cleanupModeCountDeterminesSemanticRelationIsFalse :
      cleanupModeCountDeterminesSemanticRelation ≡ false

    spectralCompressionAutomaticallyFutureSafe : Bool
    spectralCompressionAutomaticallyFutureSafeIsFalse :
      spectralCompressionAutomaticallyFutureSafe ≡ false

    consumerCollisionPermitsResidualReopening : Bool
    consumerCollisionPermitsResidualReopeningIsTrue :
      consumerCollisionPermitsResidualReopening ≡ true

canonicalNeuralSpectralRelationBoundary : NeuralSpectralRelationBoundary
canonicalNeuralSpectralRelationBoundary =
  neuralSpectralRelationBoundary
    false refl
    false refl
    false refl
    false refl
    true refl
