module DASHI.Physics.YangMills.BalabanUnifiedContinuumEndpointMarginTransportExact where

------------------------------------------------------------------------
-- ROUND65: QUANTITATIVE SAME-LIMIT ENDPOINT TRANSPORT
--
-- One continuum approximation error epsilon is used for both endpoint
-- consumers.  The exact ordered-ring arithmetic is:
--
--   delta + epsilon <= kappa4_N,
--   kappa4_N - epsilon <= kappa4_infinity
--       => delta <= kappa4_infinity;
--
--   C_N(r) <= E(r) - epsilon,
--   C_infinity(r) <= C_N(r) + epsilon
--       => C_infinity(r) <= E(r).
--
-- Thus one same-family tail modulus transports both a non-Gaussianity margin
-- and a physical clustering envelope whenever the finite-scale estimates leave
-- the corresponding buffer.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _≤_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

interactionMarginSurvivesContinuumError :
  (margin error finiteValue limitValue : ℚ) →
  margin + error ≤ finiteValue →
  finiteValue - error ≤ limitValue →
  margin ≤ limitValue
interactionMarginSurvivesContinuumError margin error finiteValue limitValue
    bufferedFinite approximation =
  let
    shifted = ℚP.+-mono-≤ bufferedFinite ℚP.≤-refl
    finiteMinus : margin ≤ finiteValue - error
    finiteMinus =
      subst
        (λ lower → lower ≤ finiteValue - error)
        (ℚRing.solve-∀ margin error)
        (subst
          (λ upper → (margin + error) + (- error) ≤ upper)
          (ℚRing.solve-∀ finiteValue error)
          shifted)
  in
  ℚP.≤-trans finiteMinus approximation

clusteringEnvelopeSurvivesContinuumError :
  (error finiteValue limitValue envelope : ℚ) →
  finiteValue ≤ envelope - error →
  limitValue ≤ finiteValue + error →
  limitValue ≤ envelope
clusteringEnvelopeSurvivesContinuumError error finiteValue limitValue envelope
    bufferedFinite approximation =
  let
    shifted = ℚP.+-mono-≤ bufferedFinite ℚP.≤-refl
    finitePlus : finiteValue + error ≤ envelope
    finitePlus =
      subst
        (λ upper → finiteValue + error ≤ upper)
        (ℚRing.solve-∀ envelope error)
        shifted
  in
  ℚP.≤-trans approximation finitePlus

record SameScaleEndpointMargins (Separation : Set) : Set₁ where
  field
    witnessScale : Nat
    continuumError : ℚ

    interactionMargin : ℚ
    finiteFourthCumulant continuumFourthCumulant : ℚ
    finiteInteractionBuffer :
      interactionMargin + continuumError ≤ finiteFourthCumulant
    fourthCumulantApproximation :
      finiteFourthCumulant - continuumError ≤ continuumFourthCumulant

    finiteConnected continuumConnected clusterEnvelope : Separation → ℚ
    finiteClusteringBuffer : ∀ separation →
      finiteConnected separation ≤ clusterEnvelope separation - continuumError
    connectedApproximation : ∀ separation →
      continuumConnected separation
      ≤ finiteConnected separation + continuumError

open SameScaleEndpointMargins public

sameLimitInteractionMargin :
  ∀ {Separation} (dataSet : SameScaleEndpointMargins Separation) →
  interactionMargin dataSet ≤ continuumFourthCumulant dataSet
sameLimitInteractionMargin dataSet =
  interactionMarginSurvivesContinuumError
    (interactionMargin dataSet)
    (continuumError dataSet)
    (finiteFourthCumulant dataSet)
    (continuumFourthCumulant dataSet)
    (finiteInteractionBuffer dataSet)
    (fourthCumulantApproximation dataSet)

sameLimitClusteringEnvelope :
  ∀ {Separation} (dataSet : SameScaleEndpointMargins Separation) separation →
  continuumConnected dataSet separation ≤ clusterEnvelope dataSet separation
sameLimitClusteringEnvelope dataSet separation =
  clusteringEnvelopeSurvivesContinuumError
    (continuumError dataSet)
    (finiteConnected dataSet separation)
    (continuumConnected dataSet separation)
    (clusterEnvelope dataSet separation)
    (finiteClusteringBuffer dataSet separation)
    (connectedApproximation dataSet separation)

sameLimitEndpointMarginTransportLevel : ProofLevel
sameLimitEndpointMarginTransportLevel = machineChecked

physicalUnifiedEndpointMarginsLevel : ProofLevel
physicalUnifiedEndpointMarginsLevel = conditional
