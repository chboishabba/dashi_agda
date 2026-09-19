{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4FiveChannelCauchyQuotientMajorantExact where

------------------------------------------------------------------------
-- CAUCHY-COEFFICIENT MAJORANT -> FOURTH-ORDER FIVE-CHANNEL BETA BOUND
--
-- This pays an actual analytic step left open by
-- BalabanYM4FiveChannelTaylorCancellationToFourthOrderExact.
--
-- After the order-0..3 Taylor coefficients vanish, write the fourth-order
-- quotient as a completed series
--
--   q(g) = sum_{n>=0} b_n(g),
--
-- and suppose the source Cauchy estimate gives, termwise,
--
--   - A r^n <= b_n(g),       0 <= r < 1.
--
-- Every finite partial quotient then obeys
--
--   - A sum_{n=0}^N r^n <= q_N(g)
--                         and
--   q_N(g) >= - A B,
--
-- for any B with (1-r) B = 1.  Order-closedness of the scalar completion
-- passes the SAME lower bound to q(g).  Thus the old direct hypothesis
--
--   -c <= q(g)
--
-- is no longer primitive: c = A B is constructed from the Cauchy coefficient
-- envelope and the strict analytic-radius margin.
--
-- For the physical application one takes r = K |g| and B = 1/(1-K|g|).
-- The finite geometric inequality itself is completely machine proved here.
-- What remains source-specific is the literal Cauchy coefficient estimate,
-- the exact Taylor-series representation of each physical channel quotient,
-- and convergence of that literal series in the chosen scalar completion.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _≤_; _<_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanYM4FiveChannelQuarticBetaAdapterExact as Five
import DASHI.Physics.YangMills.BalabanYM4FiveChannelFourthOrderFactorizationExact as Fourth
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaLowerRemainderExact as Beta

seriesPartial : (Nat → ℚ) → Nat → ℚ
seriesPartial term zero = term zero
seriesPartial term (suc cutoff) =
  term (suc cutoff) + seriesPartial term cutoff

scaledNegativeGeometricTerm : ℚ → ℚ → Nat → ℚ
scaledNegativeGeometricTerm amplitude ratio exponent =
  - (amplitude * Geo.pow ratio exponent)

scaledNegativeGeometricPartial : ℚ → ℚ → Nat → ℚ
scaledNegativeGeometricPartial amplitude ratio cutoff =
  - (amplitude * Geo.partialSum ratio cutoff)

scaledNegativeGeometricPartialStep :
  ∀ amplitude ratio cutoff →
  scaledNegativeGeometricTerm amplitude ratio (suc cutoff)
    + scaledNegativeGeometricPartial amplitude ratio cutoff
  ≡ scaledNegativeGeometricPartial amplitude ratio (suc cutoff)
scaledNegativeGeometricPartialStep amplitude ratio cutoff =
  ℚRing.solve-∀
    amplitude
    (Geo.pow ratio (suc cutoff))
    (Geo.partialSum ratio cutoff)

pointwiseCauchyLowerToFinitePartialLower :
  ∀ amplitude ratio term →
  (∀ exponent →
    scaledNegativeGeometricTerm amplitude ratio exponent ≤ term exponent) →
  ∀ cutoff →
    scaledNegativeGeometricPartial amplitude ratio cutoff
    ≤ seriesPartial term cutoff
pointwiseCauchyLowerToFinitePartialLower amplitude ratio term pointwise zero =
  pointwise zero
pointwiseCauchyLowerToFinitePartialLower amplitude ratio term pointwise (suc cutoff) =
  subst
    (λ lower →
      lower ≤ term (suc cutoff) + seriesPartial term cutoff)
    (scaledNegativeGeometricPartialStep amplitude ratio cutoff)
    (ℚP.+-mono-≤
      (pointwise (suc cutoff))
      (pointwiseCauchyLowerToFinitePartialLower
        amplitude ratio term pointwise cutoff))

scaledGeometricEnvelopeLower :
  ∀ amplitude ratio bound cutoff →
  0ℚ ≤ amplitude →
  0ℚ ≤ ratio →
  0ℚ < 1ℚ - ratio →
  (1ℚ - ratio) * bound ≡ 1ℚ →
  - (amplitude * bound)
    ≤ scaledNegativeGeometricPartial amplitude ratio cutoff
scaledGeometricEnvelopeLower
    amplitude ratio bound cutoff amplitudeNN ratioNN gapPositive inverseIdentity =
  let
    partialBelowBound :
      Geo.partialSum ratio cutoff ≤ bound
    partialBelowBound =
      Geo.geometricPartialSumBound
        ratio bound cutoff ratioNN gapPositive inverseIdentity

    scaled :
      amplitude * Geo.partialSum ratio cutoff
      ≤ amplitude * bound
    scaled =
      Norm.scaleNonnegative amplitude amplitudeNN partialBelowBound
  in
  ℚP.neg-mono-≤ scaled

cauchyFiniteQuotientLower :
  ∀ amplitude ratio bound term →
  0ℚ ≤ amplitude →
  0ℚ ≤ ratio →
  0ℚ < 1ℚ - ratio →
  (1ℚ - ratio) * bound ≡ 1ℚ →
  (∀ exponent →
    scaledNegativeGeometricTerm amplitude ratio exponent ≤ term exponent) →
  ∀ cutoff →
    - (amplitude * bound) ≤ seriesPartial term cutoff
cauchyFiniteQuotientLower amplitude ratio bound term
    amplitudeNN ratioNN gapPositive inverseIdentity pointwise cutoff =
  ℚP.≤-trans
    (scaledGeometricEnvelopeLower
      amplitude ratio bound cutoff
      amplitudeNN ratioNN gapPositive inverseIdentity)
    (pointwiseCauchyLowerToFinitePartialLower
      amplitude ratio term pointwise cutoff)

record CompletedCauchyQuotient : Set₁ where
  field
    amplitude ratio geometricBound : ℚ
    term : Nat → ℚ
    quotient : ℚ

    amplitudeNonnegative : 0ℚ ≤ amplitude
    ratioNonnegative : 0ℚ ≤ ratio
    analyticRadiusMargin : 0ℚ < 1ℚ - ratio
    geometricBoundIdentity :
      (1ℚ - ratio) * geometricBound ≡ 1ℚ

    -- This is the actual source Cauchy coefficient estimate after evaluating
    -- the coefficient at the selected physical coupling.
    cauchyCoefficientLower : ∀ exponent →
      scaledNegativeGeometricTerm amplitude ratio exponent
      ≤ term exponent

    Converges : (Nat → ℚ) → ℚ → Set
    quotientSeriesConverges :
      Converges (seriesPartial term) quotient

    -- Standard ordered-completion fact, kept separate from the YM estimate:
    -- a uniform lower bound on all finite partial sums survives the limit.
    lowerBoundClosedUnderConvergence :
      ∀ lower sequence limit →
      (∀ cutoff → lower ≤ sequence cutoff) →
      Converges sequence limit →
      lower ≤ limit

open CompletedCauchyQuotient public

completedCauchyQuotientLower :
  (dataSet : CompletedCauchyQuotient) →
  - (amplitude dataSet * geometricBound dataSet)
  ≤ quotient dataSet
completedCauchyQuotientLower dataSet =
  lowerBoundClosedUnderConvergence dataSet
    (- (amplitude dataSet * geometricBound dataSet))
    (seriesPartial (term dataSet))
    (quotient dataSet)
    (cauchyFiniteQuotientLower
      (amplitude dataSet)
      (ratio dataSet)
      (geometricBound dataSet)
      (term dataSet)
      (amplitudeNonnegative dataSet)
      (ratioNonnegative dataSet)
      (analyticRadiusMargin dataSet)
      (geometricBoundIdentity dataSet)
      (cauchyCoefficientLower dataSet))
    (quotientSeriesConverges dataSet)

completedCauchyCoefficientNonnegative :
  (dataSet : CompletedCauchyQuotient) →
  0ℚ ≤ amplitude dataSet * geometricBound dataSet
completedCauchyCoefficientNonnegative dataSet =
  let
    boundNN : 0ℚ ≤ geometricBound dataSet
    boundNN =
      let
        oneMinusNN : 0ℚ ≤ 1ℚ - ratio dataSet
        oneMinusNN = ℚP.<⇒≤ (analyticRadiusMargin dataSet)

        productIsOne :
          (1ℚ - ratio dataSet) * geometricBound dataSet ≡ 1ℚ
        productIsOne = geometricBoundIdentity dataSet

        -- Since 1-r>0 and (1-r)B=1, B cannot be negative.
        -- Rational cancellation/order gives B >= 0.
        scaledZero :
          (1ℚ - ratio dataSet) * 0ℚ
          ≤ (1ℚ - ratio dataSet) * geometricBound dataSet
        scaledZero =
          subst
            (λ right →
              (1ℚ - ratio dataSet) * 0ℚ ≤ right)
            (sym productIsOne)
            (subst
              (λ left → left ≤ 1ℚ)
              (ℚP.*-zeroʳ (1ℚ - ratio dataSet))
              (ℚP.0≤1))
        instance
          gapPositive = ℚ.positive (analyticRadiusMargin dataSet)
      in
      ℚP.*-cancelˡ-≤-pos (1ℚ - ratio dataSet) scaledZero

    instance
      amplitudeNN = nonNegative (amplitudeNonnegative dataSet)
      boundNonnegative = nonNegative boundNN
  in
  ℚP.nonNegative⁻¹
    (amplitude dataSet * geometricBound dataSet)

record FiveChannelCauchyTailData (Cell : Set) : Set₁ where
  field
    cells : Agda.Builtin.List.List Cell
    coupling : ℚ
    channelRemainder : Cell → Five.PhysicalBetaChannel → ℚ

    quotientData :
      Cell → Five.PhysicalBetaChannel → CompletedCauchyQuotient

    -- Order-0..3 cancellation has already exposed the exact fourth power.
    exactFourthOrderFactorization : ∀ cell channel →
      channelRemainder cell channel
      ≡ Beta.power4 coupling * quotient (quotientData cell channel)

open FiveChannelCauchyTailData public

asFourthOrderFactorizedFiveChannelData :
  ∀ {Cell} →
  FiveChannelCauchyTailData Cell →
  Fourth.FourthOrderFactorizedFiveChannelData Cell
asFourthOrderFactorizedFiveChannelData dataSet = record
  { Fourth.FourthOrderFactorizedFiveChannelData.cells = cells dataSet
  ; Fourth.FourthOrderFactorizedFiveChannelData.coupling = coupling dataSet
  ; Fourth.FourthOrderFactorizedFiveChannelData.channelRemainder =
      channelRemainder dataSet
  ; Fourth.FourthOrderFactorizedFiveChannelData.fourthOrderQuotient =
      λ cell channel → quotient (quotientData dataSet cell channel)
  ; Fourth.FourthOrderFactorizedFiveChannelData.coefficient =
      λ cell channel →
        amplitude (quotientData dataSet cell channel)
        * geometricBound (quotientData dataSet cell channel)
  ; Fourth.FourthOrderFactorizedFiveChannelData.exactFourthOrderFactorization =
      exactFourthOrderFactorization dataSet
  ; Fourth.FourthOrderFactorizedFiveChannelData.quotientLower =
      λ cell channel →
        completedCauchyQuotientLower (quotientData dataSet cell channel)
  ; Fourth.FourthOrderFactorizedFiveChannelData.coefficientNonnegative =
      λ cell channel →
        completedCauchyCoefficientNonnegative
          (quotientData dataSet cell channel)
  }

cauchyTailGlobalQuarticLower :
  ∀ {Cell} (dataSet : FiveChannelCauchyTailData Cell) →
  - (Five.coefficientTotal
      (Fourth.asFiveChannelQuarticBetaData
        (asFourthOrderFactorizedFiveChannelData dataSet))
      * Beta.power4 (coupling dataSet))
  ≤ Five.betaInt
      (Fourth.asFiveChannelQuarticBetaData
        (asFourthOrderFactorizedFiveChannelData dataSet))
cauchyTailGlobalQuarticLower dataSet =
  Fourth.factorizedGlobalQuarticLower
    (asFourthOrderFactorizedFiveChannelData dataSet)

finiteCauchyCoefficientGeometricMajorantLevel : ProofLevel
finiteCauchyCoefficientGeometricMajorantLevel = machineChecked

completedCauchyQuotientLowerLevel : ProofLevel
completedCauchyQuotientLowerLevel = machineChecked

cauchyFiveChannelToGlobalQuarticBetaLevel : ProofLevel
cauchyFiveChannelToGlobalQuarticBetaLevel = machineChecked

-- These are now the physical/source leaves.  The direct fourth-order quotient
-- majorant is no longer one of them.
literalFiveChannelCauchyCoefficientEstimateLevel : ProofLevel
literalFiveChannelCauchyCoefficientEstimateLevel = conditional

literalFiveChannelTaylorSeriesRepresentationLevel : ProofLevel
literalFiveChannelTaylorSeriesRepresentationLevel = conditional

literalFiveChannelSeriesConvergenceLevel : ProofLevel
literalFiveChannelSeriesConvergenceLevel = conditional

orderedRationalLimitClosureLevel : ProofLevel
orderedRationalLimitClosureLevel = standardImported
