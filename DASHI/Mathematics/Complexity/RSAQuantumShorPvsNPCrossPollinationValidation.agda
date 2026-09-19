module DASHI.Mathematics.Complexity.RSAQuantumShorPvsNPCrossPollinationValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Mathematics.Complexity.RSAQuantumShorPvsNPCrossPollinationExact as Cross

------------------------------------------------------------------------
-- Positive reused structure.
------------------------------------------------------------------------

validationSameConsumer :
  Cross.sameOrderConsumerAlreadyPaid ≡ refl
validationSameConsumer = refl

validationShorHiddenPeriod :
  Cross.shorHiddenPeriodSurfaceExists ≡ refl
validationShorHiddenPeriod = refl

validationShorFourier :
  Cross.shorFourierPeriodMachineExists ≡ refl
validationShorFourier = refl

validationHyperformalReduction :
  Cross.hyperfabricSelectedSectionReductionAvailable ≡ refl
validationHyperformalReduction = refl

validationPantsInterface :
  Cross.pantsSeamRequiresAndCarriesInterfaceMatch ≡ refl
validationPantsInterface = refl

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
