module DASHI.Moonshine.AristotleCrossPollinationRegression where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Integer using (ℤ; +_; -[1+_]; _*_; _-_)
open import Data.List.Base using (List; []; _∷_)

import Base369 as Base
import DASHI.Analysis.FiniteRealQSeriesReflectionExact as Reflection
import DASHI.Arithmetic.DecimalDigitalRootNonaryExact as Digital
import DASHI.Arithmetic.FibonacciNonaryPeriodExact as Fibonacci
import DASHI.Arithmetic.FinitePrimeProductSieveExact as ProductSieve
import DASHI.Arithmetic.SixWheelCRTExact as CRT
import DASHI.Arithmetic.SixWheelSieveCountExact as Wheel
import DASHI.Moonshine.AristotleDeltaWordT2T3FiniteParityExact as FinitePlate
import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
import DASHI.Moonshine.Hecke23AntiparallelExact as Antiparallel
import DASHI.Moonshine.RamanujanTauHecke23Exact as Tau
import DASHI.Physics.ShiftDiscreteWaveStep as Wave
import DASHI.Physics.ShiftPhaseTableInterference as Phase

decimal123DigitSumInvariant :
  Digital.decimalPositionalResidue9
    (Digital.mapDigits (Digital.d1 ∷ Digital.d2 ∷ Digital.d3 ∷ []))
  ≡
  Digital.decimalDigitSumResidue9
    (Digital.mapDigits (Digital.d1 ∷ Digital.d2 ∷ Digital.d3 ∷ []))
decimal123DigitSumInvariant =
  Digital.decimalDigitSumInvariant
    (Digital.d1 ∷ Digital.d2 ∷ Digital.d3 ∷ [])

rootNineIsZeroResidue : Digital.rootResidue9 Digital.root9 ≡ Base.non-0
rootNineIsZeroResidue = refl

fibonacciStateReturnsAtTwentyFour :
  Fibonacci.fibState 24 ≡ Fibonacci.fibStart
fibonacciStateReturnsAtTwentyFour = Fibonacci.fibStateAt24IsStart

fibonacciTriadicOffsetTwenty :
  Fibonacci.isTriadicResidue (Fibonacci.fibResidue 20) ≡ true
fibonacciTriadicOffsetTwenty = refl

sixWheelTotalSplitAtFiveBlocks :
  5 * 6 ≡ 5 * 4 + 5 * 2
sixWheelTotalSplitAtFiveBlocks = Wheel.sixBlockCountSplitsFourPlusTwo 5

twoThreeProductTotalIsSix :
  ProductSieve.totalProduct ProductSieve.twoThreeFactors ≡ 6
twoThreeProductTotalIsSix = ProductSieve.twoThreeTotalIsSix

twoThreeProductSurvivorsIsTwo :
  ProductSieve.survivorProduct ProductSieve.twoThreeFactors ≡ 2
twoThreeProductSurvivorsIsTwo = ProductSieve.twoThreeSurvivorsIsTwo

crtFiveSurvives : CRT.CRT23Survivor (CRT.r6ToCRT23 Wheel.r5)
crtFiveSurvives = CRT.r5SurvivesCRT

weight12Hecke23 :
  Hecke.heckeProductExpression 11 2 3
  ≡ Hecke.heckeTerm 1 6 ∷ []
weight12Hecke23 = Hecke.hecke23AnyWeight 11

weight12Hecke333 :
  Hecke.hecke333Weight12
  ≡ Hecke.heckeTerm 1 27 ∷ Hecke.heckeTerm 354294 3 ∷ []
weight12Hecke333 = Hecke.hecke333Weight12NormalForm

tau27Recurrence :
  Tau.tau27
  ≡ (Tau.tau3 * Tau.tau3 * Tau.tau3)
      - ((+ 2 * Tau.pow3Eleven) * Tau.tau3)
tau27Recurrence = Tau.tau27PrimeCubeRecurrence

antiparallelAtTauSix :
  (+ 21) * Antiparallel.hecke2ScaledCoefficient Tau.tau6
  ≡
  (-[1+ 1 ]) * Antiparallel.hecke3ScaledCoefficient Tau.tau6
antiparallelAtTauSix =
  Antiparallel.hecke23AntiparallelCrossMultiplied Tau.tau6

-- Direct source-parity checks imported from RequestProject.DeltaWordGraphs and
-- RequestProject.T2vsT3.  These remain finite checks, not global claims.
finiteWordMultiplierT2T3T2 :
  FinitePlate.wordMultiplierT2T3T2 ≡ + 145152
finiteWordMultiplierT2T3T2 = refl

finiteWordMultiplierT3Cubed :
  FinitePlate.wordMultiplierT3T3T3 ≡ + 16003008
finiteWordMultiplierT3Cubed = refl

finiteComparisonSample2Quotient :
  FinitePlate.integerQuotientSample FinitePlate.sample2 ≡ + 0
finiteComparisonSample2Quotient = refl

finiteComparisonSample2Remainder :
  FinitePlate.integerRemainderSample FinitePlate.sample2 ≡ + 576
finiteComparisonSample2Remainder = refl

finiteComparisonSample3Reconstructs :
  FinitePlate.wordT2Sample FinitePlate.sample3
  ≡ FinitePlate.wordT3Sample FinitePlate.sample3
      * FinitePlate.integerQuotientSample FinitePlate.sample3
      + FinitePlate.integerRemainderSample FinitePlate.sample3
finiteComparisonSample3Reconstructs =
  FinitePlate.euclideanReconstruction FinitePlate.sample3

phaseOneReflectsToPhaseThree :
  (coefficients : List ℤ) →
  Reflection.waveConj
    (Reflection.finiteQSeriesAtPhase coefficients Phase.φ1)
  ≡
  Reflection.finiteQSeriesAtPhase coefficients Phase.φ3
phaseOneReflectsToPhaseThree coefficients =
  Reflection.finiteQSeriesPhaseReflection coefficients Phase.φ1

phaseTwoFiniteSeriesIsReal :
  (coefficients : List ℤ) →
  Wave.DiscreteWave.im
    (Reflection.finiteQSeriesAtPhase coefficients Phase.φ2)
  ≡ + 0
phaseTwoFiniteSeriesIsReal = Reflection.phase2SeriesImaginaryZero
