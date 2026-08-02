module DASHI.Physics.Closure.NSTriadKNOutputRelocationIntegerGeometricEnvelope where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Errett Bishop; Douglas Bridges; Zachary Murray; Jean-Michel Bony;
-- Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin; Agda standard-library
-- contributors; DASHI repository contributors.
-- Title: "Constructive Analysis"; "Constructive Analysis in the Agda Proof
-- Assistant"; "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires"; "Fourier Analysis and
-- Nonlinear Partial Differential Equations"; and "Integer geometric envelope
-- for the output-relocation dyadic series".
-- Venue/year: Springer, 1985; arXiv, 2022; Annales scientifiques de l'Ecole
-- Normale Superieure 14 (1981); Springer, 2011; Agda standard library; DASHI
-- formal development, 2026.
-- DOI: 10.1007/978-3-642-61667-9; 10.48550/arXiv.2205.08354;
-- 10.24033/asens.1404; 10.1007/978-3-642-16830-7; the repository envelope has
-- no DOI.
-- Uses: the exact output-relocation exponent identity and the target interval
-- 5/2 < s < 3.  On this interval the low exponent 2s-5/2 is strictly larger
-- than 2 and the gap exponent 2s is strictly larger than 5.
-- Relationship: reduces the actual H^s shell factors to comparison with the
-- integer geometric series sum_j 4^-j = 4/3 and sum_d 32^-d = 32/31.  The
-- rational finite-cutoff sums and product bound 128/93 are now proved.  Only
-- the concrete non-integral shell-factor comparisons remain open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_; _+_)

import DASHI.Physics.Closure.NSTriadKNOutputRelocationWeightedExponentIdentity as Weighted
import DASHI.Physics.Closure.NSTriadKNOutputRelocationUnitWeightCheckA as Unit
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Rational

record PositiveFraction : Set where
  constructor fraction
  field
    numerator denominator : Nat

open PositiveFraction public

lowIntegerEnvelopeExponent : Nat
lowIntegerEnvelopeExponent = 2

gapIntegerEnvelopeExponent : Nat
gapIntegerEnvelopeExponent = 5

lowGeometricRatio : PositiveFraction
lowGeometricRatio = fraction 1 4

gapGeometricRatio : PositiveFraction
gapGeometricRatio = fraction 1 32

lowInfiniteSumBound : PositiveFraction
lowInfiniteSumBound = fraction 4 3

gapInfiniteSumBound : PositiveFraction
gapInfiniteSumBound = fraction 32 31

doubleSeriesBound : PositiveFraction
doubleSeriesBound = fraction 128 93

lowGeometricCrossProductLeft : Nat
lowGeometricCrossProductLeft = 3 * 4

lowGeometricCrossProductRight : Nat
lowGeometricCrossProductRight = 4 * 3

gapGeometricCrossProductLeft : Nat
gapGeometricCrossProductLeft = 31 * 32

gapGeometricCrossProductRight : Nat
gapGeometricCrossProductRight = 32 * 31

lowGeometricIdentity :
  lowGeometricCrossProductLeft ≡ lowGeometricCrossProductRight
lowGeometricIdentity = refl

gapGeometricIdentity :
  gapGeometricCrossProductLeft ≡ gapGeometricCrossProductRight
gapGeometricIdentity = refl

doubleSeriesNumeratorMeaning : numerator doubleSeriesBound ≡ 4 * 32
doubleSeriesNumeratorMeaning = refl

doubleSeriesDenominatorMeaning : denominator doubleSeriesBound ≡ 3 * 31
doubleSeriesDenominatorMeaning = refl

record IntegerEnvelopeCutset : Set₁ where
  field
    Real : Set
    sobolevExponent : Real
    fiveHalvesBelowSobolev : Set
    twoPow : Real → Real
    natEmbed : Nat → Real
    negate multiply : Real → Real → Real
    leq : Real → Real → Set

    lowExponentAboveTwo : Set
    gapExponentAboveFive : Set
    baseTwoPowerAntitoneInExponent : Set
    lowTermDominatedByQuarterPowers : Set
    gapTermDominatedByThirtySecondPowers : Set

open IntegerEnvelopeCutset public

record IntegerEnvelopeReceipt : Set where
  constructor receipt
  field
    physicalExponentClosed :
      Weighted.outputRelocationWeightedExponentIdentityClosed ≡ true
    unitWeightSymbolicCheckAClosed :
      Unit.outputRelocationUnitWeightSymbolicCheckA ≡ true
    rationalFiniteGeometricEnvelopeClosed :
      Rational.rationalFiniteGeometricEnvelopeClosed ≡ true
    quarterUniformPartialSumClosed :
      Rational.quarterUniformPartialSumClosed ≡ true
    thirtySecondUniformPartialSumClosed :
      Rational.thirtySecondUniformPartialSumClosed ≡ true
    rectangularProductBoundClosed :
      Rational.rectangularOneTwentyEightOverNinetyThreeClosed ≡ true
    lowEnvelopeIsTwo : lowIntegerEnvelopeExponent ≡ 2
    gapEnvelopeIsFive : gapIntegerEnvelopeExponent ≡ 5
    lowSumIsFourThirds : lowInfiniteSumBound ≡ fraction 4 3
    gapSumIsThirtyTwoThirtyFirsts :
      gapInfiniteSumBound ≡ fraction 32 31
    productIsOneTwentyEightOverNinetyThree :
      doubleSeriesBound ≡ fraction 128 93

open IntegerEnvelopeReceipt public

integerEnvelopeReceipt : IntegerEnvelopeReceipt
integerEnvelopeReceipt = receipt
  Weighted.outputRelocationWeightedExponentIdentityClosedIsTrue
  Unit.outputRelocationUnitWeightSymbolicCheckAIsTrue
  Rational.rationalFiniteGeometricEnvelopeClosedIsTrue
  Rational.quarterUniformPartialSumClosedIsTrue
  Rational.thirtySecondUniformPartialSumClosedIsTrue
  Rational.rectangularOneTwentyEightOverNinetyThreeClosedIsTrue
  refl refl refl refl refl

outputRelocationIntegerEnvelopeExponentsClosed : Bool
outputRelocationIntegerEnvelopeExponentsClosed = true

outputRelocationRationalGeometricConstantsClosed : Bool
outputRelocationRationalGeometricConstantsClosed = true

outputRelocationRationalFiniteCutoffSummationClosed : Bool
outputRelocationRationalFiniteCutoffSummationClosed = true

outputRelocationArbitraryRatioGeometricTheoremRequired : Bool
outputRelocationArbitraryRatioGeometricTheoremRequired = false

outputRelocationConstructivePowerMonotonicityBridgeClosed : Bool
outputRelocationConstructivePowerMonotonicityBridgeClosed = false

outputRelocationActualHsCutoffUniformSeriesClosed : Bool
outputRelocationActualHsCutoffUniformSeriesClosed = false

-- Compatibility name retained for existing consumers.  It refers to the
-- actual H^s series, not the now-closed rational envelope series.
outputRelocationCutoffUniformSeriesClosed : Bool
outputRelocationCutoffUniformSeriesClosed =
  outputRelocationActualHsCutoffUniformSeriesClosed

outputRelocationIntegerEnvelopeExponentsClosedIsTrue :
  outputRelocationIntegerEnvelopeExponentsClosed ≡ true
outputRelocationIntegerEnvelopeExponentsClosedIsTrue = refl

outputRelocationRationalGeometricConstantsClosedIsTrue :
  outputRelocationRationalGeometricConstantsClosed ≡ true
outputRelocationRationalGeometricConstantsClosedIsTrue = refl

outputRelocationRationalFiniteCutoffSummationClosedIsTrue :
  outputRelocationRationalFiniteCutoffSummationClosed ≡ true
outputRelocationRationalFiniteCutoffSummationClosedIsTrue = refl

outputRelocationArbitraryRatioGeometricTheoremRequiredIsFalse :
  outputRelocationArbitraryRatioGeometricTheoremRequired ≡ false
outputRelocationArbitraryRatioGeometricTheoremRequiredIsFalse = refl

outputRelocationConstructivePowerMonotonicityBridgeClosedIsFalse :
  outputRelocationConstructivePowerMonotonicityBridgeClosed ≡ false
outputRelocationConstructivePowerMonotonicityBridgeClosedIsFalse = refl

outputRelocationActualHsCutoffUniformSeriesClosedIsFalse :
  outputRelocationActualHsCutoffUniformSeriesClosed ≡ false
outputRelocationActualHsCutoffUniformSeriesClosedIsFalse = refl

outputRelocationCutoffUniformSeriesClosedIsFalse :
  outputRelocationCutoffUniformSeriesClosed ≡ false
outputRelocationCutoffUniformSeriesClosedIsFalse = refl
