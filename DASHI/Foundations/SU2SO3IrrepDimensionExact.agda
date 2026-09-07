module DASHI.Foundations.SU2SO3IrrepDimensionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- DASHI CONTRIBUTION
--
-- Use highest-weight integers rather than informal half-integers:
--
--   SU(2) highest weight n has dimension n+1;
--   it descends to an SO(3) representation exactly on the even-weight lane
--   used here, n = 2*j, whose dimension is 2*j+1.
--
-- This makes the p=2 boundary precise.  The two-dimensional n=1 doublet is an
-- SU(2) representation but is not on the even highest-weight SO(3)-descent
-- lane.  Every odd dimension 2*j+1 in the j=0..35 scan is.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Foundations.FiniteRepresentationRestrictionCore as Restriction

su2Dimension : Nat → Nat
su2Dimension n = suc n

data EvenHighestWeight : Nat → Set where
  evenZero : EvenHighestWeight 0
  evenStep :
    {n : Nat} →
    EvenHighestWeight n →
    EvenHighestWeight (suc (suc n))

twice : Nat → Nat
twice 0 = 0
twice (suc n) = suc (suc (twice n))

twiceIsEven : (n : Nat) → EvenHighestWeight (twice n)
twiceIsEven 0 = evenZero
twiceIsEven (suc n) = evenStep (twiceIsEven n)

spinorHighestWeightOneDoesNotDescend :
  EvenHighestWeight 1 → ⊥
spinorHighestWeightOneDoesNotDescend ()

so3Dimension : Nat → Nat
so3Dimension j = suc (twice j)

so3AsSu2HighestWeight :
  (j : Nat) →
  su2Dimension (twice j) ≡ so3Dimension j
so3AsSu2HighestWeight j = refl

spinHalfDimensionIsTwo : su2Dimension 1 ≡ 2
spinHalfDimensionIsTwo = refl

data AngularMomentum0To35 : Set where
  j0 : AngularMomentum0To35
  j1 : AngularMomentum0To35
  j2 : AngularMomentum0To35
  j3 : AngularMomentum0To35
  j4 : AngularMomentum0To35
  j5 : AngularMomentum0To35
  j6 : AngularMomentum0To35
  j7 : AngularMomentum0To35
  j8 : AngularMomentum0To35
  j9 : AngularMomentum0To35
  j10 : AngularMomentum0To35
  j11 : AngularMomentum0To35
  j12 : AngularMomentum0To35
  j13 : AngularMomentum0To35
  j14 : AngularMomentum0To35
  j15 : AngularMomentum0To35
  j16 : AngularMomentum0To35
  j17 : AngularMomentum0To35
  j18 : AngularMomentum0To35
  j19 : AngularMomentum0To35
  j20 : AngularMomentum0To35
  j21 : AngularMomentum0To35
  j22 : AngularMomentum0To35
  j23 : AngularMomentum0To35
  j24 : AngularMomentum0To35
  j25 : AngularMomentum0To35
  j26 : AngularMomentum0To35
  j27 : AngularMomentum0To35
  j28 : AngularMomentum0To35
  j29 : AngularMomentum0To35
  j30 : AngularMomentum0To35
  j31 : AngularMomentum0To35
  j32 : AngularMomentum0To35
  j33 : AngularMomentum0To35
  j34 : AngularMomentum0To35
  j35 : AngularMomentum0To35

jNat : AngularMomentum0To35 → Nat
jNat j0 = 0
jNat j1 = 1
jNat j2 = 2
jNat j3 = 3
jNat j4 = 4
jNat j5 = 5
jNat j6 = 6
jNat j7 = 7
jNat j8 = 8
jNat j9 = 9
jNat j10 = 10
jNat j11 = 11
jNat j12 = 12
jNat j13 = 13
jNat j14 = 14
jNat j15 = 15
jNat j16 = 16
jNat j17 = 17
jNat j18 = 18
jNat j19 = 19
jNat j20 = 20
jNat j21 = 21
jNat j22 = 22
jNat j23 = 23
jNat j24 = 24
jNat j25 = 25
jNat j26 = 26
jNat j27 = 27
jNat j28 = 28
jNat j29 = 29
jNat j30 = 30
jNat j31 = 31
jNat j32 = 32
jNat j33 = 33
jNat j34 = 34
jNat j35 = 35

jDimension : AngularMomentum0To35 → Nat
jDimension j = so3Dimension (jNat j)

continuousSO3Irrep :
  AngularMomentum0To35 →
  Restriction.ContinuousIrrep
continuousSO3Irrep j =
  Restriction.continuous-irrep
    (twice (jNat j))
    (jDimension j)
    "SO(3) angular-momentum irrep, recorded through even SU(2) highest weight"
    "dimension = 2*j+1; no concrete Hilbert-space basis is constructed here"

j0DimensionIsOne : jDimension j0 ≡ 1
j0DimensionIsOne = refl

j1DimensionIsThree : jDimension j1 ≡ 3
j1DimensionIsThree = refl

j3DimensionIsSeven : jDimension j3 ≡ 7
j3DimensionIsSeven = refl

j4DimensionIsNine : jDimension j4 ≡ 9
j4DimensionIsNine = refl

j35DimensionIsSeventyOne : jDimension j35 ≡ 71
j35DimensionIsSeventyOne = refl

record SU2SO3DimensionBoundary : Set where
  field
    p2RequiresSpinorialSU2Lane : Bool
    p2RequiresSpinorialSU2LaneIsTrue :
      p2RequiresSpinorialSU2Lane ≡ true

    oddDimensionsUseSO3IntegerAngularMomentumLane : Bool
    oddDimensionsUseSO3IntegerAngularMomentumLaneIsTrue :
      oddDimensionsUseSO3IntegerAngularMomentumLane ≡ true

    dimensionFormulaExplainsOggSelection : Bool
    dimensionFormulaExplainsOggSelectionIsFalse :
      dimensionFormulaExplainsOggSelection ≡ false

canonicalSU2SO3DimensionBoundary : SU2SO3DimensionBoundary
canonicalSU2SO3DimensionBoundary =
  record
    { p2RequiresSpinorialSU2Lane = true
    ; p2RequiresSpinorialSU2LaneIsTrue = refl
    ; oddDimensionsUseSO3IntegerAngularMomentumLane = true
    ; oddDimensionsUseSO3IntegerAngularMomentumLaneIsTrue = refl
    ; dimensionFormulaExplainsOggSelection = false
    ; dimensionFormulaExplainsOggSelectionIsFalse = refl
    }
