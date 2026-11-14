{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkEq223SourceSignUnderdeterminationExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _+_; -_)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K

MetricVariationToy : Set
MetricVariationToy = K.SymmetricTensorComponent4 → ℚ

positiveVacuumVariation : MetricVariationToy
positiveVacuumVariation K.component00 = 1ℚ
positiveVacuumVariation K.component11 = 1ℚ
positiveVacuumVariation K.component22 = 1ℚ
positiveVacuumVariation K.component33 = 1ℚ
positiveVacuumVariation component = 0ℚ

negativeVacuumVariation : MetricVariationToy
negativeVacuumVariation K.component00 = - 1ℚ
negativeVacuumVariation K.component11 = - 1ℚ
negativeVacuumVariation K.component22 = - 1ℚ
negativeVacuumVariation K.component33 = - 1ℚ
negativeVacuumVariation component = 0ℚ

positiveERBVariation : MetricVariationToy
positiveERBVariation = positiveVacuumVariation

negativeERBVariation : MetricVariationToy
negativeERBVariation = negativeVacuumVariation

diagonalTrace : MetricVariationToy → ℚ
diagonalTrace variation =
  (variation K.component00 + variation K.component11)
  + (variation K.component22 + variation K.component33)

positiveVacuumTraceIsFour :
  diagonalTrace positiveVacuumVariation ≡ Int.+ 4 / 1
positiveVacuumTraceIsFour = refl

negativeVacuumTraceIsMinusFour :
  diagonalTrace negativeVacuumVariation ≡ - (Int.+ 4 / 1)
negativeVacuumTraceIsMinusFour = refl

positiveERBTraceIsFour :
  diagonalTrace positiveERBVariation ≡ Int.+ 4 / 1
positiveERBTraceIsFour = refl

negativeERBTraceIsMinusFour :
  diagonalTrace negativeERBVariation ≡ - (Int.+ 4 / 1)
negativeERBTraceIsMinusFour = refl

sameBareVariationTypeAllowsOppositeVacuumSigns : Bool
sameBareVariationTypeAllowsOppositeVacuumSigns = true

sameBareVariationTypeAllowsOppositeERBSigns : Bool
sameBareVariationTypeAllowsOppositeERBSigns = true

eq223SourceTypeDoesNotDetermineVacuumSign : Bool
eq223SourceTypeDoesNotDetermineVacuumSign = true

eq223SourceTypeDoesNotDetermineERBSign : Bool
eq223SourceTypeDoesNotDetermineERBSign = true

vacuumSectorFactorizationDeterminesSignWithoutCoefficientLaw : Bool
vacuumSectorFactorizationDeterminesSignWithoutCoefficientLaw = false

sourceMetricVariationTheoremStillRequired : Bool
sourceMetricVariationTheoremStillRequired = true

birthmarkPersistenceDeterminesEq223VacuumSign : Bool
birthmarkPersistenceDeterminesEq223VacuumSign = false
