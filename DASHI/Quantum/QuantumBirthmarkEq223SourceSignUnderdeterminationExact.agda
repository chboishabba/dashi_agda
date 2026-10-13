{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkEq223SourceSignUnderdeterminationExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; -_)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K

------------------------------------------------------------------------
-- EQ.(2.23) VACUUM-SIGN UNDERDETERMINATION IN THE CURRENT SOURCE TYPE
--
-- `Eq223SourceMetricVariationRealization.vacuumMetricVariation` has the shape
-- Vacuum -> SymmetricTensorComponent4 -> Q and carries no sign law.  The same
-- bare component-function carrier therefore admits opposite diagonal traces.
------------------------------------------------------------------------

VacuumMetricVariationToy : Set
VacuumMetricVariationToy = K.SymmetricTensorComponent4 → ℚ

positiveVacuumVariation : VacuumMetricVariationToy
positiveVacuumVariation K.component00 = 1ℚ
positiveVacuumVariation K.component11 = 1ℚ
positiveVacuumVariation K.component22 = 1ℚ
positiveVacuumVariation K.component33 = 1ℚ
positiveVacuumVariation component = 0ℚ

negativeVacuumVariation : VacuumMetricVariationToy
negativeVacuumVariation K.component00 = - 1ℚ
negativeVacuumVariation K.component11 = - 1ℚ
negativeVacuumVariation K.component22 = - 1ℚ
negativeVacuumVariation K.component33 = - 1ℚ
negativeVacuumVariation component = 0ℚ

diagonalTrace : VacuumMetricVariationToy → ℚ
diagonalTrace variation =
  (variation K.component00 + variation K.component11)
  + (variation K.component22 + variation K.component33)

positiveVacuumTraceIsFour :
  diagonalTrace positiveVacuumVariation ≡ Int.+ 4
positiveVacuumTraceIsFour = refl

negativeVacuumTraceIsMinusFour :
  diagonalTrace negativeVacuumVariation ≡ - (Int.+ 4)
negativeVacuumTraceIsMinusFour = refl

sameBareVariationTypeAllowsOppositeVacuumSigns : Bool
sameBareVariationTypeAllowsOppositeVacuumSigns = true

eq223SourceTypeDoesNotDetermineVacuumSign : Bool
eq223SourceTypeDoesNotDetermineVacuumSign = true

vacuumSectorFactorizationDeterminesSignWithoutCoefficientLaw : Bool
vacuumSectorFactorizationDeterminesSignWithoutCoefficientLaw = false

sourceMetricVariationTheoremStillRequired : Bool
sourceMetricVariationTheoremStillRequired = true

birthmarkPersistenceDeterminesEq223VacuumSign : Bool
birthmarkPersistenceDeterminesEq223VacuumSign = false
