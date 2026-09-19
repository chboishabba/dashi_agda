module DASHI.Mathematics.Complexity.RSAQuantumShorPvsNPCrossPollinationValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.Complexity.RSAQuantumShorPvsNPCrossPollinationExact as Cross

------------------------------------------------------------------------
-- Positive reused structure.
------------------------------------------------------------------------

validationProducerVerifierSeparation :
  Cross.producerVerifierSeparationPresent
    Cross.canonicalPvsNPRSAQuantumCrossPollinationBoundary
  ≡ true
validationProducerVerifierSeparation = refl

validationModelFibreSeparation :
  Cross.computationalModelFibreSeparationPresent
    Cross.canonicalPvsNPRSAQuantumCrossPollinationBoundary
  ≡ true
validationModelFibreSeparation = refl

validationShorReductionTemplate :
  Cross.shorSymmetryReductionTemplatePresent
    Cross.canonicalPvsNPRSAQuantumCrossPollinationBoundary
  ≡ true
validationShorReductionTemplate = refl

validationRecoverableQuotient :
  Cross.recoverableQuotientInfrastructurePresent
    Cross.canonicalPvsNPRSAQuantumCrossPollinationBoundary
  ≡ true
validationRecoverableQuotient = refl

validationHyperformalReduction :
  Cross.hyperfabricConsumerReductionInfrastructurePresent
    Cross.canonicalPvsNPRSAQuantumCrossPollinationBoundary
  ≡ true
validationHyperformalReduction = refl

validationExplicitSeamCompatibility :
  Cross.explicitSeamCompatibilityInfrastructurePresent
    Cross.canonicalPvsNPRSAQuantumCrossPollinationBoundary
  ≡ true
validationExplicitSeamCompatibility = refl

------------------------------------------------------------------------
-- Fail-closed frontier.
------------------------------------------------------------------------

validationPvsNPOpen :
  Cross.classicalPvsNPResolved
    Cross.canonicalPvsNPRSAQuantumCrossPollinationBoundary
  ≡ false
validationPvsNPOpen = refl

validationCookLevinOpen :
  Cross.genericCookLevinCNFPolynomialityPaid
    Cross.canonicalPvsNPRSAQuantumCrossPollinationBoundary
  ≡ false
validationCookLevinOpen = refl

validationUniformRecoveryOpen :
  Cross.uniformClassicalRecoveryForNPCompleteWitnessesPaid
    Cross.canonicalPvsNPRSAQuantumCrossPollinationBoundary
  ≡ false
validationUniformRecoveryOpen = refl

validationClassicalLowerBoundOpen :
  Cross.classicalSuperPolynomialLowerBoundPaid
    Cross.canonicalPvsNPRSAQuantumCrossPollinationBoundary
  ≡ false
validationClassicalLowerBoundOpen = refl
