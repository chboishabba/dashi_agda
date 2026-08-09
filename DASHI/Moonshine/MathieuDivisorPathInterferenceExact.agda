module DASHI.Moonshine.MathieuDivisorPathInterferenceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Serge Lang,
-- "Algebraic Number Theory", second edition, Springer, 1994.
-- DOI: 10.1007/978-1-4612-0853-2.
--
-- DASHI CONTRIBUTION
--
-- Upgrade divisor-path confluence from incidence bookkeeping to an exact
-- finite amplitude model.  Two distinct prime-coloured histories reaching
-- the same divisor receive independent Eisenstein amplitudes.  Their node
-- amplitude is the coherent sum and its norm splits into two diagonal terms
-- plus the exact cross term.  This is a mathematical amplitude decoration of
-- the divisor lattice; it is not asserted to be physical quantum dynamics.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_)

import DASHI.Biology.EisensteinNineRingInterferenceExact as Eisenstein
import DASHI.Moonshine.MathieuDivisorLatticeExact as Divisor

record ConfluentHistoryPair : Set where
  constructor confluentHistoryPair
  field
    leftHistory : Divisor.FactorHistory
    rightHistory : Divisor.FactorHistory
    sameEndpoint :
      Divisor.endpoint leftHistory ≡ Divisor.endpoint rightHistory

open ConfluentHistoryPair public

canonicalTwoThreeConfluence : ConfluentHistoryPair
canonicalTwoThreeConfluence =
  confluentHistoryPair
    Divisor.historyTwoThree
    Divisor.historyThreeTwo
    Divisor.historiesShareEndpoint

record HistoryAmplitudePair : Set where
  constructor historyAmplitudePair
  field
    confluence : ConfluentHistoryPair
    leftAmplitude : Eisenstein.Eisenstein
    rightAmplitude : Eisenstein.Eisenstein

open HistoryAmplitudePair public

nodeAmplitude : HistoryAmplitudePair → Eisenstein.Eisenstein
nodeAmplitude pair =
  Eisenstein.add (leftAmplitude pair) (rightAmplitude pair)

nodeIntensity : HistoryAmplitudePair → ℚ
nodeIntensity pair = Eisenstein.norm (nodeAmplitude pair)

diagonalIntensity : HistoryAmplitudePair → ℚ
diagonalIntensity pair =
  Eisenstein.norm (leftAmplitude pair)
  + Eisenstein.norm (rightAmplitude pair)

pathCrossTerm : HistoryAmplitudePair → ℚ
pathCrossTerm pair =
  Eisenstein.crossTerm (leftAmplitude pair) (rightAmplitude pair)

nodeInterferenceIdentity :
  (pair : HistoryAmplitudePair) →
  nodeIntensity pair
  ≡ diagonalIntensity pair + pathCrossTerm pair
nodeInterferenceIdentity
  (historyAmplitudePair histories left right) =
  Eisenstein.normPolarization left right

canonicalPhaseDecoratedConfluence : HistoryAmplitudePair
canonicalPhaseDecoratedConfluence =
  historyAmplitudePair
    canonicalTwoThreeConfluence
    Eisenstein.one
    Eisenstein.omega

canonicalHistoriesReachSix :
  Divisor.endpoint
    (leftHistory (confluence canonicalPhaseDecoratedConfluence))
  ≡ 6
canonicalHistoriesReachSix = refl

canonicalNodeIntensityIsOne :
  nodeIntensity canonicalPhaseDecoratedConfluence ≡ + 1
canonicalNodeIntensityIsOne = refl

canonicalDiagonalIntensityIsTwo :
  diagonalIntensity canonicalPhaseDecoratedConfluence ≡ + 2
canonicalDiagonalIntensityIsTwo = refl

canonicalPathCrossIsMinusOne :
  pathCrossTerm canonicalPhaseDecoratedConfluence ≡ 0ℚ - (+ 1)
canonicalPathCrossIsMinusOne = refl

canonicalInterferenceLedger :
  diagonalIntensity canonicalPhaseDecoratedConfluence
  + pathCrossTerm canonicalPhaseDecoratedConfluence
  ≡ + 1
canonicalInterferenceLedger = refl

record DivisorPathInterferenceBoundary : Set where
  constructor divisorPathInterferenceBoundary
  field
    amplitudesAreAdditionalDecoration : Bool
    amplitudesAreAdditionalDecorationIsTrue :
      amplitudesAreAdditionalDecoration ≡ true
    divisorIncidenceDeterminesAmplitude : Bool
    divisorIncidenceDeterminesAmplitudeIsFalse :
      divisorIncidenceDeterminesAmplitude ≡ false
    endpointConfluenceAndCoherentSumAreExact : Bool
    endpointConfluenceAndCoherentSumAreExactIsTrue :
      endpointConfluenceAndCoherentSumAreExact ≡ true
    modelIsPhysicalQuantumDynamics : Bool
    modelIsPhysicalQuantumDynamicsIsFalse :
      modelIsPhysicalQuantumDynamics ≡ false

canonicalDivisorPathInterferenceBoundary : DivisorPathInterferenceBoundary
canonicalDivisorPathInterferenceBoundary =
  divisorPathInterferenceBoundary true refl false refl true refl false refl
