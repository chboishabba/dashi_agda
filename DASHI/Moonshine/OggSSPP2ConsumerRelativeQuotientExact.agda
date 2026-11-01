module DASHI.Moonshine.OggSSPP2ConsumerRelativeQuotientExact where

------------------------------------------------------------------------
-- p=2 CONSUMER-RELATIVE QUOTIENT SAFETY
--
-- DASHI CONTRIBUTION
--
-- The five-state NineOrbit projection is neither globally "right" nor globally
-- "wrong".  It is sufficient exactly for consumers whose queries factor
-- through that projection.
--
-- This module gives three explicit grades:
--
--   * inner-orbit query: factors through the five-state quotient;
--   * orientation query: does not factor through the five-state quotient;
--   * exact-state query: does not factor through the five-state quotient.
--
-- The full dependent codec (NineOrbit + StrictSignedSide residual) reopens the
-- ten-state carrier exactly.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Moonshine.OggSSPSmallCharacteristicResidualGroupoidExact as Small
import DASHI.Moonshine.OggSSPSmallCharacteristicResidualCodecExact as Codec
import DASHI.Moonshine.QuadraticApproximationPrimeCompressionBidiExact as Compression
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic

------------------------------------------------------------------------
-- 1. Consumer query family.
------------------------------------------------------------------------

data P2Query : Set where
  innerOrbitQuestion : P2Query
  orientationQuestion : P2Query
  exactStateQuestion : P2Query

P2Answer : P2Query -> Set
P2Answer innerOrbitQuestion = Triadic.NineOrbit
P2Answer orientationQuestion = Compression.StrictSignedSide
P2Answer exactStateQuestion = Small.P2ResidualObject

askP2 :
  (query : P2Query) ->
  Small.P2ResidualObject ->
  P2Answer query
askP2 innerOrbitQuestion state = Codec.p2Project state
askP2 orientationQuestion state = Codec.p2Residual state
askP2 exactStateQuestion state = state

p2Questions :
  Query.InquiryQuestionFamily Small.P2ResidualObject P2Query
p2Questions =
  Query.inquiryQuestionFamily P2Answer askP2

------------------------------------------------------------------------
-- 2. The inner-orbit query factors exactly through the five-state quotient.
------------------------------------------------------------------------

innerOrbitFactorsThroughFive :
  Query.FactorsThrough
    p2Questions
    Codec.p2Project
    innerOrbitQuestion
innerOrbitFactorsThroughFive =
  Query.factorsThrough
    (λ orbit -> orbit)
    (λ state -> refl)

------------------------------------------------------------------------
-- 3. Orientation cannot factor through the five-state quotient.
------------------------------------------------------------------------

lowerState :
  Triadic.NineOrbit ->
  Small.P2ResidualObject
lowerState orbit =
  Compression.lowerSide , orbit

upperState :
  Triadic.NineOrbit ->
  Small.P2ResidualObject
upperState orbit =
  Compression.upperSide , orbit

orientationDoesNotFactorThroughFive :
  Query.FactorsThrough
    p2Questions
    Codec.p2Project
    orientationQuestion
  ->
  ⊥
orientationDoesNotFactorThroughFive factor =
  impossible
  where
    chosenOrbit : Triadic.NineOrbit
    chosenOrbit = Triadic.zeroOrbit

    lowerEq :
      Compression.lowerSide
      ≡ Query.quotientAnswer factor chosenOrbit
    lowerEq =
      Query.factorisation factor (lowerState chosenOrbit)

    upperEq :
      Compression.upperSide
      ≡ Query.quotientAnswer factor chosenOrbit
    upperEq =
      Query.factorisation factor (upperState chosenOrbit)

    impossible :
      ⊥
    impossible =
      lowerNotUpper
        (trans lowerEq (sym upperEq))

    lowerNotUpper :
      Compression.lowerSide ≡ Compression.upperSide -> ⊥
    lowerNotUpper ()

------------------------------------------------------------------------
-- 4. Exact state cannot factor through the five-state quotient.
------------------------------------------------------------------------

exactStateDoesNotFactorThroughFive :
  Query.FactorsThrough
    p2Questions
    Codec.p2Project
    exactStateQuestion
  ->
  ⊥
exactStateDoesNotFactorThroughFive factor =
  impossible
  where
    chosenOrbit : Triadic.NineOrbit
    chosenOrbit = Triadic.zeroOrbit

    lowerEq :
      lowerState chosenOrbit
      ≡ Query.quotientAnswer factor chosenOrbit
    lowerEq =
      Query.factorisation factor (lowerState chosenOrbit)

    upperEq :
      upperState chosenOrbit
      ≡ Query.quotientAnswer factor chosenOrbit
    upperEq =
      Query.factorisation factor (upperState chosenOrbit)

    lowerUpperEqual :
      lowerState chosenOrbit ≡ upperState chosenOrbit
    lowerUpperEqual =
      trans lowerEq (sym upperEq)

    impossible :
      ⊥
    impossible =
      Codec.lowerNotUpper chosenOrbit lowerUpperEqual

------------------------------------------------------------------------
-- 5. Full dependent codec pays exact reconstruction.
------------------------------------------------------------------------

fullCodecReopens :
  (state : Small.P2ResidualObject) ->
  Codec.p2Decode (Codec.p2Encode state) ≡ state
fullCodecReopens =
  Codec.p2DecodeEncodeExact

------------------------------------------------------------------------
-- 6. Consumer-relative policy boundary.
------------------------------------------------------------------------

data FiveOrbitQuotientUniversallySufficient : Set where
data ExactReopeningMeansEveryConsumerNeedsOrientation : Set where

fiveOrbitQuotientIsNotUniversallySufficient :
  FiveOrbitQuotientUniversallySufficient -> ⊥
fiveOrbitQuotientIsNotUniversallySufficient ()

exactReopeningDoesNotMeanEveryConsumerNeedsOrientation :
  ExactReopeningMeansEveryConsumerNeedsOrientation -> ⊥
exactReopeningDoesNotMeanEveryConsumerNeedsOrientation ()

record P2ConsumerRelativeQuotientBoundary : Set where
  constructor p2-consumer-relative-quotient-boundary
  field
    fiveOrbitQueryFactors : Bool
    orientationQueryFactors : Bool
    exactStateQueryFactors : Bool
    dependentCodecReopensExactly : Bool
    fiveOrbitQuotientUniversallySufficient : Bool
    orientationAlwaysRequiredForEveryConsumer : Bool

canonicalP2ConsumerRelativeQuotientBoundary :
  P2ConsumerRelativeQuotientBoundary
canonicalP2ConsumerRelativeQuotientBoundary =
  p2-consumer-relative-quotient-boundary
    true false false true false false
