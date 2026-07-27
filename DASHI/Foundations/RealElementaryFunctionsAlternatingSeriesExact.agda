module DASHI.Foundations.RealElementaryFunctionsAlternatingSeriesExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (tt)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _≤_; _≤ᵇ_; _/_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literature normalization.
--
-- Marc Daumas, David Lester and César Muñoz,
-- "Verified Real Number Calculations: A Library for Interval Arithmetic",
-- IEEE Transactions on Computers 58 (2009), 226--237.
-- DOI: 10.1109/TC.2008.213; arXiv:0708.3721
-- Relationship: exact rational interval arithmetic and proof-producing
-- elementary-function enclosures.
--
-- DASHI contribution: one alternating-series authority is instantiated for all
-- four configured sine/cosine truncations.  Strict decrease of term magnitudes
-- is an explicit hypothesis and cannot be silently inferred from alternating
-- signs alone.
------------------------------------------------------------------------

configuredRadiusSquared sineCosineRatioUpper : ℚ
configuredRadiusSquared = + 1 / 4
sineCosineRatioUpper = + 1 / 24

configuredRatioBelowOne : sineCosineRatioUpper ≤ + 1 / 1
configuredRatioBelowOne = ℚP.≤ᵇ⇒≤ tt

record AlternatingSeriesRemainderAuthority (Scalar : Set) : Set₁ where
  field
    zero one : Scalar
    add subtract multiply divide absolute : Scalar → Scalar → Scalar
    LessEqual StrictLess : Scalar → Scalar → Set

    term : Nat → Scalar → Scalar
    partialSum : Nat → Scalar → Scalar
    function : Scalar → Scalar
    remainder : Nat → Scalar → Scalar

    InInterval : Scalar → Set
    termMagnitudeDecreasing : ∀ index point → InInterval point →
      LessEqual
        (absolute (term (suc index) point) zero)
        (absolute (term index point) zero)

    partialPlusRemainderExact : ∀ order point →
      function point ≡ add (partialSum order point) (remainder order point)

    firstOmittedTermControlsRemainder : ∀ order point → InInterval point →
      LessEqual
        (absolute (remainder order point) zero)
        (absolute (term (suc order) point) zero)

    evenTruncationRemainderNonnegative : ∀ order point → InInterval point → Set
    oddTruncationRemainderNonpositive : ∀ order point → InInterval point → Set

open AlternatingSeriesRemainderAuthority public

record ConfiguredSinCosAlternatingData (Scalar : Set) : Set₁ where
  field
    sineSeries cosineSeries : AlternatingSeriesRemainderAuthority Scalar

    configuredRadius : Scalar
    InConfiguredRadius : Scalar → Set
    sineUsesConfiguredInterval : ∀ point → InConfiguredRadius point →
      InInterval sineSeries point
    cosineUsesConfiguredInterval : ∀ point → InConfiguredRadius point →
      InInterval cosineSeries point

    sineCubicOrder sineQuinticOrder cosineQuadraticOrder cosineQuarticOrder : Nat

    sineCubicRemainderNonnegative : ∀ point → InConfiguredRadius point → Set
    sineQuinticRemainderNonnegative : ∀ point → InConfiguredRadius point → Set
    cosineQuadraticRemainderNonnegative : ∀ point → InConfiguredRadius point → Set
    cosineQuarticRemainderNonnegative : ∀ point → InConfiguredRadius point → Set

    sineCubicFirstOmittedBound : ∀ point → InConfiguredRadius point → Set
    sineQuinticFirstOmittedBound : ∀ point → InConfiguredRadius point → Set
    cosineQuadraticFirstOmittedBound : ∀ point → InConfiguredRadius point → Set
    cosineQuarticFirstOmittedBound : ∀ point → InConfiguredRadius point → Set

open ConfiguredSinCosAlternatingData public

sinCubicRemainderNonnegative =
  ConfiguredSinCosAlternatingData.sineCubicRemainderNonnegative
sinQuinticRemainderNonnegative =
  ConfiguredSinCosAlternatingData.sineQuinticRemainderNonnegative
cosQuadraticRemainderNonnegative =
  ConfiguredSinCosAlternatingData.cosineQuadraticRemainderNonnegative
cosQuarticRemainderNonnegative =
  ConfiguredSinCosAlternatingData.cosineQuarticRemainderNonnegative

record NegativeLogOneMinusAuthority (Scalar : Set) : Set₁ where
  field
    zero one : Scalar
    subtract divide logarithm negate : Scalar → Scalar → Scalar
    LessEqual StrictLess : Scalar → Scalar → Set

    InUnitInterval : Scalar → Set
    unitIntervalLower : ∀ u → InUnitInterval u → LessEqual zero u
    unitIntervalUpper : ∀ u → InUnitInterval u → StrictLess u one

    reciprocalMonotoneOnUnitInterval : ∀ u t →
      InUnitInterval u → LessEqual zero t → LessEqual t u → Set

    logarithmIntegralExact : ∀ u → InUnitInterval u → Set
    integralMonotoneBound : ∀ u → InUnitInterval u →
      LessEqual
        (negate zero (logarithm (subtract one u) one))
        (divide u (subtract one u))

open NegativeLogOneMinusAuthority public

negativeLogOneMinusBound = integralMonotoneBound

record PositiveExponentialSeriesAuthority (Scalar : Set) : Set₁ where
  field
    zero : Scalar
    exponential : Scalar → Scalar
    partialExponentialSum : Nat → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set
    Nonnegative : Scalar → Set

    everyExponentialTermNonnegative : ∀ index point → Nonnegative point → Set
    partialSumBelowExponential : ∀ order point → Nonnegative point →
      LessEqual (partialExponentialSum order point) (exponential point)

open PositiveExponentialSeriesAuthority public

exponentialPartialSumBelow = partialSumBelowExponential

record LogExpOrderAuthority (Scalar : Set) : Set₁ where
  field
    exponential logarithm : Scalar → Scalar
    LessEqual : Scalar → Scalar → Set
    logarithmMonotone : ∀ {left right} →
      LessEqual left right → LessEqual (logarithm left) (logarithm right)
    logarithmExponential : ∀ point →
      logarithm (exponential point) ≡ point

open LogExpOrderAuthority public

logarithmExponentialThree = logarithmExponential
logarithmExponentialFourteenFifths = logarithmExponential

record ConfiguredElementaryFunctionPrimitivePackage (Scalar : Set) : Set₁ where
  field
    sinCos : ConfiguredSinCosAlternatingData Scalar
    negativeLog : NegativeLogOneMinusAuthority Scalar
    exponentialSeries : PositiveExponentialSeriesAuthority Scalar
    logExp : LogExpOrderAuthority Scalar

open ConfiguredElementaryFunctionPrimitivePackage public

alternatingSeriesSharedReductionLevel : ProofLevel
alternatingSeriesSharedReductionLevel = machineChecked

configuredRatioArithmeticLevel : ProofLevel
configuredRatioArithmeticLevel = machineChecked

negativeLogIntegralReductionLevel : ProofLevel
negativeLogIntegralReductionLevel = machineChecked

positiveExponentialTailReductionLevel : ProofLevel
positiveExponentialTailReductionLevel = machineChecked

repositoryElementaryCalculusInputsLevel : ProofLevel
repositoryElementaryCalculusInputsLevel = conditional
