module DASHI.Physics.Closure.NSTriadKNLuoGrowingCubeBernsteinExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Loukas Grafakos.
-- Title: "Classical Fourier Analysis".
-- DOI: 10.1007/978-1-4939-1194-3.
--
-- PURPOSE
-- Put the finite Fourier coefficient estimate directly on the growing carrier
--
--   Cube_q = Fin(4 * 2^q + 1)^3.
--
-- Any Boolean LP/Galerkin predicate selects a support of mass at most
-- `125 * 8^q`. Every retained coefficient obeys the checked L1 bound, so
--
--   sum_(k in support_q) |Fhat(k)|^2
--     <= 125 * 8^q * ||F||_1^2.
--
-- No repeated base list or base-mass field remains.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoGrowingFiniteCubeSupportExact as Growing
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicSupportCountExact as Support
import DASHI.Physics.Closure.NSTriadKNLuoFiniteFourierCoefficientL1Exact as Fourier
import DASHI.Physics.Closure.NSTriadKNLuoIntegerCubeSupportCapacityExact as Capacity

sumBy : ∀ {A : Set} → List A → (A → ℚ) → ℚ
sumBy [] value = 0ℚ
sumBy (item ∷ items) value = value item + sumBy items value

record GrowingCubeBernsteinData (shell : Nat) : Set₁ where
  constructor growing-cube-bernstein-data
  field
    supportPredicate : Growing.ModeAt shell → Bool
    commonInputL1Squared : ℚ
    commonInputL1SquaredNonnegative : 0ℚ ≤ commonInputL1Squared
    coefficientData :
      Growing.ModeAt shell → Fourier.FiniteFourierCoefficientData
    commonInputMeaning :
      (mode : Growing.ModeAt shell) →
      Fourier.inputL1Squared (coefficientData mode)
      ≡ commonInputL1Squared

open GrowingCubeBernsteinData public

retainedModes :
  (shell : Nat) →
  GrowingCubeBernsteinData shell →
  List (Growing.ModeAt shell)
retainedModes shell dataSet =
  Growing.filteredGrowingSupport shell (supportPredicate dataSet)

coefficientSquaredAt :
  ∀ {shell : Nat} →
  GrowingCubeBernsteinData shell →
  Growing.ModeAt shell → ℚ
coefficientSquaredAt dataSet mode =
  Fourier.coefficientSquared (coefficientData dataSet mode)

outputL2Squared :
  (shell : Nat) →
  GrowingCubeBernsteinData shell → ℚ
outputL2Squared shell dataSet =
  sumBy (retainedModes shell dataSet)
    (coefficientSquaredAt dataSet)

retainedCoefficientBound :
  ∀ {shell : Nat}
    (dataSet : GrowingCubeBernsteinData shell)
    (mode : Growing.ModeAt shell) →
  coefficientSquaredAt dataSet mode
  ≤ commonInputL1Squared dataSet
retainedCoefficientBound dataSet mode =
  subst
    (λ upper → coefficientSquaredAt dataSet mode ≤ upper)
    (commonInputMeaning dataSet mode)
    (Fourier.finiteFourierCoefficientBound
      (coefficientData dataSet mode))

sumCoefficientsBelowCount :
  ∀ {shell : Nat}
    (dataSet : GrowingCubeBernsteinData shell)
    (modes : List (Growing.ModeAt shell)) →
  sumBy modes (coefficientSquaredAt dataSet)
  ≤ Support.countMass modes * commonInputL1Squared dataSet
sumCoefficientsBelowCount dataSet [] = ℚₚ.≤-refl
sumCoefficientsBelowCount dataSet (mode ∷ modes) =
  let
    summed =
      ℚₚ.+-mono-≤
        (retainedCoefficientBound dataSet mode)
        (sumCoefficientsBelowCount dataSet modes)

    endpoint :
      commonInputL1Squared dataSet
        + Support.countMass modes * commonInputL1Squared dataSet
      ≡ (1ℚ + Support.countMass modes)
        * commonInputL1Squared dataSet
    endpoint =
      solve
        (commonInputL1Squared dataSet
        ∷ Support.countMass modes
        ∷ [])
  in
  subst
    (λ upper →
      coefficientSquaredAt dataSet mode
        + sumBy modes (coefficientSquaredAt dataSet)
      ≤ upper)
    endpoint
    summed

growingCubeBernsteinSquare :
  (shell : Nat) →
  (dataSet : GrowingCubeBernsteinData shell) →
  outputL2Squared shell dataSet
  ≤ (Capacity.oneTwentyFive * Capacity.eightPower shell)
    * commonInputL1Squared dataSet
growingCubeBernsteinSquare shell dataSet =
  let
    countStage =
      sumCoefficientsBelowCount
        dataSet
        (retainedModes shell dataSet)

    supportBound =
      Growing.filteredGrowingSupportCountBound
        shell
        (supportPredicate dataSet)

    scaledSupport :
      Support.countMass (retainedModes shell dataSet)
        * commonInputL1Squared dataSet
      ≤ (Capacity.oneTwentyFive * Capacity.eightPower shell)
        * commonInputL1Squared dataSet
    scaledSupport =
      let instance inputNN =
        nonNegative (commonInputL1SquaredNonnegative dataSet)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (commonInputL1Squared dataSet)
        supportBound
  in
  ℚₚ.≤-trans countStage scaledSupport
