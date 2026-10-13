{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkEq223SignLeafExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_; _<_)

------------------------------------------------------------------------
-- PREFERRED Eq.(2.23) SIGN LEAF
--
-- The existing CMP119 vacuum-dominance compiler has already reduced the source
-- sign problem to exactly two literal sector inequalities:
--
--   0 < N_V      (literal vacuum metric-variation coefficient)
--   0 <= N_ERB   (literal E/R/B numerator)
--
-- All subsequent sign transport to R136, continuum trace, active stress, and
-- positive acceleration is existing theorem machinery.
------------------------------------------------------------------------

record PreferredEq223LiteralSignLeaf : Set where
  constructor preferred-eq223-literal-sign-leaf
  field
    vacuumCoefficient : ℚ
    erbNumerator : ℚ
    vacuumCoefficientPositive : 0ℚ < vacuumCoefficient
    erbNumeratorNonnegative : 0ℚ ≤ erbNumerator

open PreferredEq223LiteralSignLeaf public

preferredSignReducedToTwoLiteralInequalities : Bool
preferredSignReducedToTwoLiteralInequalities = true

additionalTensorSignChoiceRequired : Bool
additionalTensorSignChoiceRequired = false

birthmarkPersistenceProvesVacuumCoefficientPositive : Bool
birthmarkPersistenceProvesVacuumCoefficientPositive = false

birthmarkPersistenceProvesERBNonnegative : Bool
birthmarkPersistenceProvesERBNonnegative = false

sourceNativeVacuumCoefficientPositivityStillRequired : Bool
sourceNativeVacuumCoefficientPositivityStillRequired = true

sourceNativeERBNonnegativityStillRequired : Bool
sourceNativeERBNonnegativityStillRequired = true
