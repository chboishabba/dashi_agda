module DASHI.Physics.YangMills.BalabanUnifiedContinuumEndpointMarginTransportExact where

------------------------------------------------------------------------
-- ROUND65: QUANTITATIVE SAME-LIMIT ENDPOINT TRANSPORT
--
-- A unified continuum norm is useful only if its error modulus is strong enough
-- to preserve the strict endpoint inequalities required downstream.  Mere
-- convergence does not by itself preserve a positive lower bound with a named
-- margin, nor an exponential-clustering upper bound with a named envelope.
--
-- This file proves the exact arithmetic needed by the four-package strategy:
-- use ONE continuum approximation error epsilon at ONE sufficiently deep scale
-- for both consumers.
--
-- Interaction survival:
--
--   delta + epsilon <= kappa4_N
--   kappa4_N - epsilon <= kappa4_infinity
--   -------------------------------------
--   delta <= kappa4_infinity.
--
-- Clustering survival:
--
--   C_N(r) <= E(r) - epsilon
--   C_infinity(r) <= C_N(r) + epsilon
--   ----------------------------------
--   C_infinity(r) <= E(r).
--
-- Thus a single same-family tail modulus can transport both non-Gaussianity
-- margin and physical separation decay, provided the finite-scale estimates
-- leave the corresponding buffer.  There is no proof-splicing between limits.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _≤_)
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
  ℚP.≤-trans
    (subst
      (λ upper → margin ≤ upper)
      (ℚRing.solve-∀ margin error)
      (ℚP.+-monoʳ-≤ error bufferedFinite))
    approximation
  where
  -- Adding -error to margin+error <= finiteValue gives margin <= finite-error.
  -- The standard rational monotonicity theorem is used in the helper below.
  ℚP.+-monoʳ-≤ : ∀ shift {left right} → left ≤ right → left + shift ≤ right + shift
  ℚP.+-monoʳ-≤ shift inequality = ℚP.+-mono-≤ inequality ℚP.≤-refl

clusteringEnvelopeSurvivesContinuumError :
  (error finiteValue limitValue envelope : ℚ) →
  finiteValue ≤ envelope - error →
  limitValue ≤ finiteValue + error →
  limitValue ≤ envelope
clusteringEnvelopeSurvivesContinuumError error finiteValue limitValue envelope
    bufferedFinite approximation =
  ℚP.≤-trans approximation
    (subst
      (λ upper → finiteValue + error ≤ upper)
      (ℚRing.solve-∀ envelope error)
      (ℚP.+-monoˡ-≤ error bufferedFinite))
  where
  ℚP.+-monoˡ-≤ : ∀ shift {left right} → left ≤ right → shift + left ≤ shift + right
  ℚP.+-monoˡ-≤ shift inequality = ℚP.+-mono-≤ ℚP.≤-refl inequality

------------------------------------------------------------------------
-- Same-scale, same-error package consumed by the unified continuum theorem.
------------------------------------------------------------------------

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

-- Physical input remaining: obtain the SAME continuum error modulus from the
-- unified Yang--Mills polymer/Schwinger norm and finite-scale margins/buffers
-- from the literal RG family.  The order arithmetic above is no longer part of
-- the research frontier.
physicalUnifiedEndpointMarginsLevel : ProofLevel
physicalUnifiedEndpointMarginsLevel = conditional
