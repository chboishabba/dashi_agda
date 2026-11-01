module DASHI.Core.AdaptiveFidelityConsumerMarginExact where

------------------------------------------------------------------------
-- ADAPTIVE FIDELITY IS DECISION-RELATIVE
--
-- A surrogate need not be globally accurate.  It is sufficient for a declared
-- consumer when the measured/bounded high-vs-low-fidelity discrepancy lies
-- inside a region on which that consumer's decision is invariant.  This turns
-- fidelity escalation into a theorem-bearing decision rather than a fixed
-- "always run the expensive model" policy.
--
-- Literature calibration:
--
-- Marc C. Kennedy and Anthony O'Hagan,
-- "Predicting the output from a complex computer code when fast
-- approximations are available", Biometrika 87(1), 2000, 1-13.
-- DOI: 10.1093/biomet/87.1.1.
--
-- Natalia M. Alexandrov, J. E. Dennis Jr., Robert M. Lewis, Virginia Torczon,
-- "A trust-region framework for managing the use of approximation models in
-- optimization", Structural Optimization 15 (1998), 16-23.
-- DOI: 10.1007/BF01197433.
--
-- Kennedy--O'Hagan motivates discrepancy modelling; Alexandrov et al. motivate
-- local trust.  The exact consumer-margin theorem below is the DASHI layer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List)

------------------------------------------------------------------------
-- Low/high fidelity comparison.
------------------------------------------------------------------------

record FidelityPair (Input Summary : Set) : Set₁ where
  constructor fidelityPair
  field
    low : Input → Summary
    high : Input → Summary
    lowModel : String
    highModel : String

open FidelityPair public

record BoundedDiscrepancy
    {Input Summary : Set}
    (pair : FidelityPair Input Summary) : Set₁ where
  constructor boundedDiscrepancy
  field
    WithinBound : Summary → Summary → Set
    boundReference : String
    boundEvidence : List String
    bounded : ∀ input → WithinBound (low pair input) (high pair input)

open BoundedDiscrepancy public

------------------------------------------------------------------------
-- Consumer margin.  `DecisionStable` is deliberately a relation rather than a
-- global metric assumption: each consumer states the region over which its own
-- decision is invariant.
------------------------------------------------------------------------

record ConsumerDecisionMargin
    {Summary Decision : Set}
    (decide : Summary → Decision) : Set₁ where
  constructor consumerDecisionMargin
  field
    InsideMargin : Summary → Summary → Set
    decisionStable :
      ∀ {predicted actual} →
      InsideMargin predicted actual →
      decide predicted ≡ decide actual
    marginReference : String

open ConsumerDecisionMargin public

record FidelityInsideConsumerMargin
    {Input Summary Decision : Set}
    {pair : FidelityPair Input Summary}
    (discrepancy : BoundedDiscrepancy pair)
    {decide : Summary → Decision}
    (margin : ConsumerDecisionMargin decide) : Set₁ where
  constructor fidelityInsideConsumerMargin
  field
    boundImpliesMargin :
      ∀ {predicted actual} →
      WithinBound discrepancy predicted actual →
      InsideMargin margin predicted actual

open FidelityInsideConsumerMargin public

------------------------------------------------------------------------
-- Core theorem: if the fidelity error is inside the consumer's invariant
-- region, low- and high-fidelity evaluation induce exactly the same decision.
------------------------------------------------------------------------

lowFidelityDecisionIsSafe :
  ∀ {Input Summary Decision}
    {pair : FidelityPair Input Summary}
    (discrepancy : BoundedDiscrepancy pair)
    {decide : Summary → Decision}
    (margin : ConsumerDecisionMargin decide)
    (inside : FidelityInsideConsumerMargin discrepancy margin)
    (input : Input) →
  decide (low pair input) ≡ decide (high pair input)
lowFidelityDecisionIsSafe discrepancy margin inside input =
  decisionStable margin
    (boundImpliesMargin inside (bounded discrepancy input))

------------------------------------------------------------------------
-- Escalation is required when we do not possess the theorem above.  Failure to
-- certify the margin is not evidence that the low-fidelity answer is wrong; it
-- is an information/fidelity obligation.
------------------------------------------------------------------------

data FidelityDisposition : Set where
  acceptLowFidelity : FidelityDisposition
  escalateHighFidelity : FidelityDisposition

record FidelityEscalationCertificate
    {Input Summary Decision : Set}
    (pair : FidelityPair Input Summary)
    (decide : Summary → Decision) : Set₁ where
  constructor fidelityEscalationCertificate
  field
    inputReference : String
    disposition : FidelityDisposition
    discrepancyEvidence : List String
    consumerMarginEvidence : List String
    highFidelityMaterialisationRecorded : Bool

open FidelityEscalationCertificate public

record AdaptiveFidelityBoundary : Set where
  constructor adaptiveFidelityBoundary
  field
    smallGlobalErrorNotRequiredWhenDecisionMarginCertified : Bool
    missingMarginCertificateMeansEscalationNotRefutation : Bool
    discrepancyMustBeIndexedByModelPairAndRegion : Bool
    consumerRiskDeterminesRequiredFidelity : Bool
    highFidelityObservationCanUpdateFutureLowFidelityTrust : Bool

canonicalAdaptiveFidelityBoundary : AdaptiveFidelityBoundary
canonicalAdaptiveFidelityBoundary =
  adaptiveFidelityBoundary true true true true true
