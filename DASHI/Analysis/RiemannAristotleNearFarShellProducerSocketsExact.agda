module DASHI.Analysis.RiemannAristotleNearFarShellProducerSocketsExact where

------------------------------------------------------------------------
-- S2 PRODUCER SOCKETS
--
-- Forward side:
--   the Lean owner now supplies a uniform reflection-pair curvature constant and
--   a summable delta^-2 shell carrier.
--
-- Backward side:
--   the near/far compiler needs actual scalar budgets B_far(J), B_near(J) whose
--   sum lies below the surviving cluster margin.
--
-- These records force those two analyses to meet without conflating
-- convergence with quantitative cancellation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; _*_; _≤_)

record FarShellQuantitativeEnvelope : Set where
  constructor far-shell-quantitative-envelope
  field
    farCutoff : Nat
    farContribution curvatureConstant tailMass farBudget : ℚ
    farContributionBound : farContribution ≤ farBudget
    curvatureTailBudgetIdentity : farBudget ≡ curvatureConstant * tailMass

open FarShellQuantitativeEnvelope public

record FiniteSignedNearShellCore : Set where
  constructor finite-signed-near-shell-core
  field
    nearCutoff nearShellCount : Nat
    signedNearContribution nearBudget : ℚ
    nearCarrierFinite : Bool
    nearCarrierFiniteIsTrue : nearCarrierFinite ≡ true
    signedAggregateBound : signedNearContribution ≤ nearBudget

open FiniteSignedNearShellCore public

record CompatibleNearFarProducers
    (near : FiniteSignedNearShellCore)
    (far : FarShellQuantitativeEnvelope) : Set where
  constructor compatible-near-far-producers
  field
    sameCutoff : nearCutoff near ≡ farCutoff far

open CompatibleNearFarProducers public

record NearFarProducerBoundary : Set where
  constructor near-far-producer-boundary
  field
    uniformCurvatureSourceOwnedInLean : Bool
    uniformCurvatureSourceOwnedInLeanIsTrue :
      uniformCurvatureSourceOwnedInLean ≡ true
    deltaSquaredTailSummabilityOwnedInLean : Bool
    deltaSquaredTailSummabilityOwnedInLeanIsTrue :
      deltaSquaredTailSummabilityOwnedInLean ≡ true
    explicitNumericFarTailEnvelopeTransportedToAgda : Bool
    explicitNumericFarTailEnvelopeTransportedToAgdaIsFalse :
      explicitNumericFarTailEnvelopeTransportedToAgda ≡ false
    finiteSignedNearShellEstimateClosed : Bool
    finiteSignedNearShellEstimateClosedIsFalse :
      finiteSignedNearShellEstimateClosed ≡ false
    nearAbsoluteMajorantAcceptedAsCompletion : Bool
    nearAbsoluteMajorantAcceptedAsCompletionIsFalse :
      nearAbsoluteMajorantAcceptedAsCompletion ≡ false

canonicalNearFarProducerBoundary : NearFarProducerBoundary
canonicalNearFarProducerBoundary =
  near-far-producer-boundary true refl true refl false refl false refl false refl
