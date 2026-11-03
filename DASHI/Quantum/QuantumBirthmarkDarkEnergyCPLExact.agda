{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkDarkEnergyCPLExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

cplW : ℚ → ℚ → ℚ → ℚ
cplW w0 wa scaleFactor =
  w0 + wa * (1ℚ - scaleFactor)

lcdmW : ℚ → ℚ
lcdmW scaleFactor = cplW (- 1ℚ) 0ℚ scaleFactor

lcdmIsConstantMinusOne :
  (scaleFactor : ℚ) →
  lcdmW scaleFactor ≡ - 1ℚ
lcdmIsConstantMinusOne scaleFactor = solve (scaleFactor ∷ [])

presentEpochW :
  (w0 wa : ℚ) →
  cplW w0 wa 1ℚ ≡ w0
presentEpochW w0 wa = solve (w0 ∷ wa ∷ [])

earlyScaleFactorZeroW :
  (w0 wa : ℚ) →
  cplW w0 wa 0ℚ ≡ w0 + wa
earlyScaleFactorZeroW w0 wa = solve (w0 ∷ wa ∷ [])

record HistoryCPLPrediction : Set where
  constructor history-cpl-prediction
  field
    w0 : ℚ
    wa : ℚ
    microscopicHistoryDerivation : Bool
    surveyFitPerformed : Bool

open HistoryCPLPrediction public

historyCPLCarrierOwned : Bool
historyCPLCarrierOwned = true

lcdmNullOwned : Bool
lcdmNullOwned = true

nonzeroWaUniquelyIdentifiesHistorySector : Bool
nonzeroWaUniquelyIdentifiesHistorySector = false

historySectorW0WaDerived : Bool
historySectorW0WaDerived = false

DESICanConstrainCarrier : Bool
DESICanConstrainCarrier = true

EuclidCanConstrainCarrier : Bool
EuclidCanConstrainCarrier = true

RomanCanConstrainCarrier : Bool
RomanCanConstrainCarrier = true
