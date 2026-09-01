module DASHI.Physics.Closure.NSTriadKNDeterministicNestedColumnWeightRound332Exact where

------------------------------------------------------------------------
-- ROUND332 / REVERSE COLUMN ALSO DETERMINES THE R295 CELL WEIGHT
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNCellRateSwapInvariantWeightRound295Exact as R295

F : C3.RealField _
F = Rational.rationalRealField

sameNestedColumnForcesSameRate :
  (rho : Z3.FourierMode → ℚ)
  (inner outer₁ outer₂ : Physical.PhysicalTriadIncidence) →
  Physical.k inner ≡ Physical.p outer₁ →
  Physical.k inner ≡ Physical.p outer₂ →
  Physical.q outer₁ ≡ Physical.q outer₂ →
  R295.cellRate rho outer₁ ≡ R295.cellRate rho outer₂
sameNestedColumnForcesSameRate rho inner outer₁ outer₂ glue₁ glue₂ qSame =
  cong₂Add
    (trans (symmetry glue₁) glue₂)
    qSame
  where
  symmetry : ∀ {a b : Z3.FourierMode} → a ≡ b → b ≡ a
  symmetry refl = refl

  cong₂Add :
    ∀ {a b c d : Z3.FourierMode} →
    a ≡ b → c ≡ d →
    rho a + rho c ≡ rho b + rho d
  cong₂Add refl refl = refl

sameNestedColumnForcesSameWeight :
  (rho : Z3.FourierMode → ℚ)
  (phi : ℚ → C3.Complex F)
  (inner outer₁ outer₂ : Physical.PhysicalTriadIncidence) →
  Physical.k inner ≡ Physical.p outer₁ →
  Physical.k inner ≡ Physical.p outer₂ →
  Physical.q outer₁ ≡ Physical.q outer₂ →
  R295.rateWeight rho phi outer₁ ≡ R295.rateWeight rho phi outer₂
sameNestedColumnForcesSameWeight rho phi inner outer₁ outer₂ glue₁ glue₂ qSame =
  cong phi
    (sameNestedColumnForcesSameRate
      rho inner outer₁ outer₂ glue₁ glue₂ qSame)

round332NestedColumnRateDeterministic : Bool
round332NestedColumnRateDeterministic = true

round332NestedColumnAbstractR295WeightDeterministic : Bool
round332NestedColumnAbstractR295WeightDeterministic = true

round332IndependentColumnWeightMultiplicityRemains : Bool
round332IndependentColumnWeightMultiplicityRemains = false

round332HeatExponentialRealizationInstalledHere : Bool
round332HeatExponentialRealizationInstalledHere = false

round332NumericalColumnBudgetClosed : Bool
round332NumericalColumnBudgetClosed = false

round332WeightedRowBudgetClosed : Bool
round332WeightedRowBudgetClosed = false

round332PackageAClosed : Bool
round332PackageAClosed = false

round332ClayPromotion : Bool
round332ClayPromotion = false
