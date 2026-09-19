module DASHI.Mathematics.Complexity.RSAQuantumShorPvsNPCrossPollinationValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.Complexity.RSAQuantumShorPvsNPCrossPollinationExact as Cross
import DASHI.Mathematics.Complexity.PolynomialFactorisationCostExact
import DASHI.Mathematics.Complexity.SATDecisionToWitnessSelfReductionExact
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact

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

validationCostAwareFactorisation :
  Cross.costAwareFactorisationCompilerPresent
    Cross.canonicalPvsNPRSAQuantumCrossPollinationBoundary
  ≡ true
validationCostAwareFactorisation = refl

validationDecisionSearchEngine :
  Cross.decisionToSearchSelfReductionEnginePresent
    Cross.canonicalPvsNPRSAQuantumCrossPollinationBoundary
  ≡ true
validationDecisionSearchEngine = refl

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

validationBooleanFormulaSATInstantiation :
  Cross.booleanFormulaSATSelfReductionInstantiationPaid
    Cross.canonicalPvsNPRSAQuantumCrossPollinationBoundary
  ≡ true
validationBooleanFormulaSATInstantiation = refl

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
