module DASHI.Biology.TraumaRelationalLearningNonpromotionExact where

------------------------------------------------------------------------
-- TRAUMA / RELATIONAL LEARNING NON-PROMOTION
--
-- A learned relational predictor or adaptive capacity does not make harmful
-- exposure beneficial and does not establish that exposure caused superior
-- integrative capacity.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.TrialecticMemoryLearningHyperfabricExact as Trialectic

traumaExposureDoesNotImplyEnhancedIntegration =
  Trialectic.traumaExposureDoesNotImplyEnhancedIntegration

adaptiveCapacityDoesNotMakeExposureBeneficial =
  Trialectic.adaptiveCapacityDoesNotMakeExposureBeneficial

record TraumaRelationalLearningBoundary : Set where
  constructor trauma-relational-learning-boundary
  field
    traumaAutomaticallyEnhancesIntegration : Bool
    adaptiveCapacityMakesExposureBeneficial : Bool
    learningMayChangePolicyWithoutMemoryErasure : Bool

canonicalTraumaRelationalLearningBoundary :
  TraumaRelationalLearningBoundary
canonicalTraumaRelationalLearningBoundary =
  trauma-relational-learning-boundary false false true
