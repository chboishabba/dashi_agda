module DASHI.Physics.Plasma.LoureiroBetaZeroCrossoverComputationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; zero; _*_; _-_)
open import Data.Nat.DivMod using (_/_)

------------------------------------------------------------------------
-- COMPUTED BETA=0 SPECIALISATION OF BOLDYREV-LOUREIRO SCALINGS
--
-- Source family:
--   lambda_c/L ~ S_L ^ (-(4 - 5 beta)/(7 - 20 beta/3))
--   E(k_perp) ~ k_perp ^ (-11/5 + 2 beta/3)
--
-- This file owns only the finite beta=0 arithmetic specialization.
------------------------------------------------------------------------

betaZero : Nat
betaZero = 0

crossoverNumerator : Nat → Nat
crossoverNumerator beta = 4 - (5 * beta)

crossoverDenominator : Nat → Nat
crossoverDenominator beta = 7 - ((20 * beta) / 3)

spectrumNumeratorBetaZero : Nat
spectrumNumeratorBetaZero = 11

spectrumDenominatorBetaZero : Nat
spectrumDenominatorBetaZero = 5

betaZeroCrossoverNumerator : crossoverNumerator betaZero ≡ 4
betaZeroCrossoverNumerator = refl

betaZeroCrossoverDenominator : crossoverDenominator betaZero ≡ 7
betaZeroCrossoverDenominator = refl

betaZeroSpectrumNumerator : spectrumNumeratorBetaZero ≡ 11
betaZeroSpectrumNumerator = refl

betaZeroSpectrumDenominator : spectrumDenominatorBetaZero ≡ 5
betaZeroSpectrumDenominator = refl

record BetaZeroComputedScaling : Set where
  constructor beta-zero-computed-scaling
  field
    crossoverNumeratorValue : Nat
    crossoverDenominatorValue : Nat
    spectrumNumeratorValue : Nat
    spectrumDenominatorValue : Nat
    crossoverNumeratorChecked : crossoverNumeratorValue ≡ 4
    crossoverDenominatorChecked : crossoverDenominatorValue ≡ 7
    spectrumNumeratorChecked : spectrumNumeratorValue ≡ 11
    spectrumDenominatorChecked : spectrumDenominatorValue ≡ 5

canonicalBetaZeroComputedScaling : BetaZeroComputedScaling
canonicalBetaZeroComputedScaling =
  beta-zero-computed-scaling
    (crossoverNumerator betaZero)
    (crossoverDenominator betaZero)
    spectrumNumeratorBetaZero
    spectrumDenominatorBetaZero
    betaZeroCrossoverNumerator
    betaZeroCrossoverDenominator
    betaZeroSpectrumNumerator
    betaZeroSpectrumDenominator

record LoureiroBetaZeroComputationBoundary : Set where
  constructor loureiro-beta-zero-computation-boundary
  field
    fourSeventhsIsNowComputedFromBetaZeroFamily : Bool
    fourSeventhsIsNowComputedFromBetaZeroFamilyIsTrue :
      fourSeventhsIsNowComputedFromBetaZeroFamily ≡ true
    elevenFifthsIsNowComputedAtBetaZero : Bool
    elevenFifthsIsNowComputedAtBetaZeroIsTrue :
      elevenFifthsIsNowComputedAtBetaZero ≡ true
    thisArithmeticProvesPhysicalTearingAssumptions : Bool
    thisArithmeticProvesPhysicalTearingAssumptionsIsFalse :
      thisArithmeticProvesPhysicalTearingAssumptions ≡ false
    natFormulaRepresentsGeneralRealBetaFamily : Bool
    natFormulaRepresentsGeneralRealBetaFamilyIsFalse :
      natFormulaRepresentsGeneralRealBetaFamily ≡ false

canonicalLoureiroBetaZeroComputationBoundary : LoureiroBetaZeroComputationBoundary
canonicalLoureiroBetaZeroComputationBoundary =
  loureiro-beta-zero-computation-boundary true refl true refl false refl false refl
