module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406PositiveEndpointAmplitudeMaxCutExact where

------------------------------------------------------------------------
-- POSITIVE B7 / E+ OUTPUT AGGREGATION WITHOUT CARDINALITY TAX
--
-- R461 reduces one fixed-output positive Cauchy endpoint to
--
--   F_k^+ <= W * a_k^2
--
-- for a nonnegative amplitude sum a_k on that output fibre.  The remaining
-- finite-output aggregation does not require an output-count factor:
--
--   sum_k F_k^+
--     <= W * sum_k a_k^2
--     <= W * (sum_k a_k)^2.
--
-- This owner proves the second/global algebra abstractly.  Consequently the
-- genuine E+ analytic leaf can be concentrated on one cutoff-uniform bound for
-- the total physical amplitude sum on the literal companion family.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational

two : ℚ
two = 1ℚ + 1ℚ

record PositiveOutputEndpointFamily (Output : Set) : Set₁ where
  constructor positive-output-endpoint-family
  field
    ceiling : ℚ
    ceilingNN : 0ℚ ≤ ceiling
    amplitude : Output → ℚ
    amplitudeNN : (output : Output) → 0ℚ ≤ amplitude output
    positiveFlux : Output → ℚ
    positiveFluxPaid :
      (output : Output) →
      positiveFlux output
      ≤ ceiling * (amplitude output * amplitude output)

open PositiveOutputEndpointFamily public

sumAmplitude :
  ∀ {Output} → PositiveOutputEndpointFamily Output → List Output → ℚ
sumAmplitude P [] = 0ℚ
sumAmplitude P (output ∷ rest) =
  amplitude P output + sumAmplitude P rest

sumPositiveFlux :
  ∀ {Output} → PositiveOutputEndpointFamily Output → List Output → ℚ
sumPositiveFlux P [] = 0ℚ
sumPositiveFlux P (output ∷ rest) =
  positiveFlux P output + sumPositiveFlux P rest

sumAmplitudeNN :
  ∀ {Output}
    (P : PositiveOutputEndpointFamily Output)
    (outputs : List Output) →
  0ℚ ≤ sumAmplitude P outputs
sumAmplitudeNN P [] = ℚP.≤-refl
sumAmplitudeNN P (output ∷ rest) =
  ℚP.+-mono-≤ (amplitudeNN P output) (sumAmplitudeNN P rest)

crossGapNN :
  ∀ {Output}
    (P : PositiveOutputEndpointFamily Output)
    (a s : ℚ) →
    0ℚ ≤ a → 0ℚ ≤ s →
  0ℚ ≤ two * ceiling P * (a * s)
crossGapNN P a s aNN sNN =
  let
    twoNN : 0ℚ ≤ two
    twoNN = ℚP.+-mono-≤ ℚP.≤-refl ℚP.≤-refl
    twoWNN : 0ℚ ≤ two * ceiling P
    twoWNN = Rational.productNonnegative twoNN (ceilingNN P)
    asNN : 0ℚ ≤ a * s
    asNN = Rational.productNonnegative aNN sNN
  in
  Rational.productNonnegative twoWNN asNN

sumPositiveFluxBelowAmplitudeSquare :
  ∀ {Output}
    (P : PositiveOutputEndpointFamily Output)
    (outputs : List Output) →
  sumPositiveFlux P outputs
  ≤ ceiling P * (sumAmplitude P outputs * sumAmplitude P outputs)
sumPositiveFluxBelowAmplitudeSquare P [] =
  subst
    (0ℚ ≤_)
    (solve (ceiling P ∷ []))
    ℚP.≤-refl
sumPositiveFluxBelowAmplitudeSquare P (output ∷ rest) =
  let
    W = ceiling P
    a = amplitude P output
    s = sumAmplitude P rest

    headPaid = positiveFluxPaid P output
    tailPaid = sumPositiveFluxBelowAmplitudeSquare P rest
    added = ℚP.+-mono-≤ headPaid tailPaid

    base = W * (a * a) + W * (s * s)
    gap = two * W * (a * s)

    baseMeaning :
      W * (a * a) + W * (s * s) ≡ base
    baseMeaning = refl

    gapNN : 0ℚ ≤ gap
    gapNN = crossGapNN P a s (amplitudeNN P output) (sumAmplitudeNN P rest)

    baseLeExpanded : base ≤ base + gap
    baseLeExpanded =
      subst
        (λ lower → lower ≤ base + gap)
        (ℚP.+-identityʳ base)
        (ℚP.+-monoʳ-≤ base gapNN)

    endpoint :
      base + gap ≡ W * ((a + s) * (a + s))
    endpoint = solve (W ∷ a ∷ s ∷ [])

    paidToBase : sumPositiveFlux P (output ∷ rest) ≤ base
    paidToBase = subst
      (sumPositiveFlux P (output ∷ rest) ≤_)
      baseMeaning
      added

    paidToSquare :
      sumPositiveFlux P (output ∷ rest)
      ≤ W * ((a + s) * (a + s))
    paidToSquare =
      ℚP.≤-trans paidToBase
        (subst (base ≤_) endpoint baseLeExpanded)
  in
  paidToSquare

------------------------------------------------------------------------
-- Status / exact research seam.
------------------------------------------------------------------------

ePositiveOutputAggregationClosed : Bool
ePositiveOutputAggregationClosed = true

ePositiveOutputAggregationIntroducesCardinalityFactor : Bool
ePositiveOutputAggregationIntroducesCardinalityFactor = false

eGlobalAmplitudeSumProducerClosedHere : Bool
eGlobalAmplitudeSumProducerClosedHere = false

ePositiveEndpointAggregationIntroducesEstimate : Bool
ePositiveEndpointAggregationIntroducesEstimate = false

clayPromotion : Bool
clayPromotion = false

ePositiveOutputAggregationClosedIsTrue :
  ePositiveOutputAggregationClosed ≡ true
ePositiveOutputAggregationClosedIsTrue = refl

ePositiveOutputAggregationIntroducesCardinalityFactorIsFalse :
  ePositiveOutputAggregationIntroducesCardinalityFactor ≡ false
ePositiveOutputAggregationIntroducesCardinalityFactorIsFalse = refl

eGlobalAmplitudeSumProducerClosedHereIsFalse :
  eGlobalAmplitudeSumProducerClosedHere ≡ false
eGlobalAmplitudeSumProducerClosedHereIsFalse = refl
