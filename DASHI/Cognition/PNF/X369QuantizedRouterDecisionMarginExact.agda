module DASHI.Cognition.PNF.X369QuantizedRouterDecisionMarginExact where

------------------------------------------------------------------------
-- P0: score-quantization interval -> strict cross-boundary ordering.
--
-- Reuses the original integer directed-head error identity from
-- X369DirectedRouterConditionalCodecExact and the existing consumer
-- margin/fidelity programme. The score-error *magnitude* is NOT
-- postulated from a particular quantizer here: source quantizers must
-- supply independently checked enclosures [lower,upper].
--
-- Score intervals and selected sets are finite and explicitly typed.
-- A strict separation between every selected lower envelope and every
-- unselected upper envelope proves cross-boundary selection stability.
-- It does NOT preserve mixture weights, signed FFN outputs or histories.
-- No kernel check yet: SymPy is only algebraic CI stand-in.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Fin using (Fin)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Cognition.PNF.X369DirectedRouterConditionalCodecExact as Original
import DASHI.Core.ConsumerRelativeApproximateFidelityBridgeExact as Approx
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

record QuantizedRouterIntervals (E : Nat) : Set where
  constructor quantizedRouterIntervals
  field
    sourceScore : Fin E → Nat
    quantizedScore : Fin E → Nat
    lowerEnvelope : Fin E → Nat
    upperEnvelope : Fin E → Nat
    sourceSelected : Fin E → Bool
    sourceScoreInsideInterval :
      (e : Fin E) →
      lowerEnvelope e ≤ sourceScore e
      × sourceScore e ≤ upperEnvelope e
    quantizedScoreInsideInterval :
      (e : Fin E) →
      lowerEnvelope e ≤ quantizedScore e
      × quantizedScore e ≤ upperEnvelope e
    strictSourceSelectedAgainstUnselected :
      (i j : Fin E) →
      sourceSelected i ≡ true →
      sourceSelected j ≡ false →
      upperEnvelope j < lowerEnvelope i
open QuantizedRouterIntervals public

-- The strict margin certificate proves both source and quantized
-- cross-boundary order. The source set is assumed to be the
-- admitted, original deterministic TopK set; this proof is about
-- the set's cross-boundary separation, not internal rank order.
quantizedSelectedOutranksUnselected :
  ∀ {E : Nat} →
  (certificate : QuantizedRouterIntervals E) →
  (i j : Fin E) →
  sourceSelected certificate i ≡ true →
  sourceSelected certificate j ≡ false →
  quantizedScore certificate j < quantizedScore certificate i
quantizedSelectedOutranksUnselected certificate i j selected unselected =
  <-≤-trans
    (≤-<-trans
      (proj₂ (quantizedScoreInsideInterval certificate j))
      (strictSourceSelectedAgainstUnselected certificate i j
         selected unselected))
    (proj₁ (quantizedScoreInsideInterval certificate i))

originalSelectedOutranksUnselected :
  ∀ {E : Nat} →
  (certificate : QuantizedRouterIntervals E) →
  (i j : Fin E) →
  sourceSelected certificate i ≡ true →
  sourceSelected certificate j ≡ false →
  sourceScore certificate j < sourceScore certificate i
originalSelectedOutranksUnselected certificate i j selected unselected =
  <-≤-trans
    (≤-<-trans
      (proj₂ (sourceScoreInsideInterval certificate j))
      (strictSourceSelectedAgainstUnselected certificate i j
         selected unselected))
    (proj₁ (sourceScoreInsideInterval certificate i))

-- No tie across source-selected versus unselected is possible under
-- this strict certificate. TopK set equality additionally uses the
-- original finite 'exactly k selected' admission and the unchanged
-- deterministic TopK meaning. The proof deliberately does not
-- conflate a Boolean selection mask with ordered expert slots.

------------------------------------------------------------------------
-- Counterexample: exact original one-feature channel is insufficient
-- on the general directed source; after dropping its reverse-sensitive
-- fibre a downstream score may flip with no visible code difference.
-- This reuses the SOURCE witness, not a synthetic 'bad code' claim.
------------------------------------------------------------------------

originalTwoChannelCollisionBlocksReverseConsumer :
  Descent.ConsumerSufficient
    Original.encodeDirectedTwo Original.reverseConsumer → ⊥
originalTwoChannelCollisionBlocksReverseConsumer =
  Original.twoDirectedWithoutDCNotSufficient

-- Existing reusable approximate consumer owner is deliberately
-- imported rather than redefined. The finite margin theorem above
-- supplies exactly the strict inter-expert order that an admitted
-- source quantizer must maintain. Full ApproximateDecisionCertificate
-- needs an original source bound and real semantics to instantiate.

------------------------------------------------------------------------
-- Exact finite "decision at the boundary" counterexample:
-- two experts have initial scores (1,0) but quantized (0,1).
-- There is no universal rank preservation without a strict
-- certified inequality (or an explicit exact equality).
------------------------------------------------------------------------

originalFirstScore : Nat
originalFirstScore = 1

originalSecondScore : Nat
originalSecondScore = 0

quantizedFirstScore : Nat
quantizedFirstScore = 0

quantizedSecondScore : Nat
quantizedSecondScore = 1

originalStrictlyRanksFirst :
  originalSecondScore < originalFirstScore
originalStrictlyRanksFirst = s≤s z≤n

quantizedStrictlyRanksSecond :
  quantizedFirstScore < quantizedSecondScore
quantizedStrictlyRanksSecond = s≤s z≤n

-- The example warns against claiming score-level equality or
-- top-k safety from any sub-threshold unverified rounding tolerance.
