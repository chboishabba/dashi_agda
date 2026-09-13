module DASHI.Physics.ExoticGravity.AntigravityNegativeGClaimComparisonWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Physics.ExoticGravity.AntigravityNegativeGPairedComparatorExact as SignedPair
import DASHI.Physics.ExoticGravity.AntigravityClaimTheoryComparisonExact as Claim
import DASHI.Physics.ExoticGravity.AntigravityUnificationInteractionExact as Unified
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- NEGATIVE-G PAIR -> EXISTING CLAIM-INDEXED THEORY COMPARISON
--
-- The generic alternative-gravity slot must be exactly the -G prediction if a
-- consumer says it is evaluating the negative-G hypothesis.  A field merely
-- named "modified prediction" is not sufficient.
------------------------------------------------------------------------

record NegativeGClaimComparisonWeld
    (claim : Anti.AntigravityClaim) : Set where
  constructor negative-g-claim-comparison-weld
  field
    signedPair : SignedPair.SignedGPairedPrediction claim
    claimComparison : Claim.ClaimIndexedTheoryComparison claim

    positiveGIsOrdinaryComparisonPrediction :
      SignedPair.positiveGPrediction signedPair
        ≡ Unified.ordinaryGRPrediction (Claim.comparison claimComparison)

    negativeGIsAlternativeComparisonPrediction :
      SignedPair.negativeGPrediction signedPair
        ≡ Unified.modifiedGravityPrediction (Claim.comparison claimComparison)

open NegativeGClaimComparisonWeld public

------------------------------------------------------------------------
-- Reverse residuals.
------------------------------------------------------------------------

data NegativeGClaimComparisonResidual : Set where
  missingSignedGPair : NegativeGClaimComparisonResidual
  missingClaimIndexedComparison : NegativeGClaimComparisonResidual
  missingPositiveGOrdinarySlotIdentity : NegativeGClaimComparisonResidual
  missingNegativeGAlternativeSlotIdentity : NegativeGClaimComparisonResidual
  missingNegativeGSpecificResidualAssessment : NegativeGClaimComparisonResidual

producerForNegativeGClaimComparisonResidual :
  NegativeGClaimComparisonResidual → Search.ProducerClass
producerForNegativeGClaimComparisonResidual missingSignedGPair = Search.propositionSourceProducer
producerForNegativeGClaimComparisonResidual missingClaimIndexedComparison = Search.discriminatorProducer
producerForNegativeGClaimComparisonResidual missingPositiveGOrdinarySlotIdentity = Search.identityProducer
producerForNegativeGClaimComparisonResidual missingNegativeGAlternativeSlotIdentity = Search.identityProducer
producerForNegativeGClaimComparisonResidual missingNegativeGSpecificResidualAssessment = Search.contradictionProducer

record NegativeGClaimComparisonBoundary : Set where
  constructor negative-g-claim-comparison-boundary
  field
    genericModifiedGravitySlotAutomaticallyMeansNegativeG : Bool
    exactPositiveGOrdinarySlotIdentityRequired : Bool
    exactNegativeGAlternativeSlotIdentityRequired : Bool
    sameClaimComparisonMustConsumeBothSignedPredictions : Bool
    negativeGComparisonMayReuseUnrelatedModifiedPrediction : Bool
    negativeGComparisonAutomaticallyProvesNegativeGPhysics : Bool
    negativeGComparisonAutomaticallyProvesAntigravity : Bool

canonicalNegativeGClaimComparisonBoundary : NegativeGClaimComparisonBoundary
canonicalNegativeGClaimComparisonBoundary =
  negative-g-claim-comparison-boundary false true true true false false false
