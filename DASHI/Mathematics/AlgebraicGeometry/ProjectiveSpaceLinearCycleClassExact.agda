module DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceLinearCycleClassExact where

------------------------------------------------------------------------
-- RATIONAL LINEAR-SUBSPACE CYCLE CLASSES ON THE FINITE CP^n HODGE BASIS
--
-- ProjectiveSpaceHodgeBasisExact already owns the standard finite basis
--
--   1, H, ..., H^n
--
-- with H^p of Hodge bidegree (p,p).  This file adds the corresponding
-- rational linear-cycle model: in codimension p, a rational multiple of the
-- coordinate linear subspace P^(n-p) maps to the rational multiple of H^p.
--
-- The cycle-class map is therefore surjective in every represented
-- codimension.  This is theorem-bearing algebra on the existing CP^n Hodge
-- basis; identifying it with singular/de Rham cohomology of the literal
-- quotient CP^n remains the separate geometric same-object theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceHodgeBasisExact as Basis

record CPnRationalLinearCycle
    (n : Nat) (power : Basis.ProjectiveSpaceHodgeBasis n) : Set where
  constructor linearCycle
  field
    cycleCoefficient : ℚ

open CPnRationalLinearCycle public

record CPnRationalHodgeClass
    (n : Nat) (power : Basis.ProjectiveSpaceHodgeBasis n) : Set where
  constructor hodgeClass
  field
    hodgeCoefficient : ℚ

open CPnRationalHodgeClass public

zeroLinearCycle :
  ∀ {n power} → CPnRationalLinearCycle n power
zeroLinearCycle = linearCycle 0ℚ

addLinearCycle :
  ∀ {n power} →
  CPnRationalLinearCycle n power →
  CPnRationalLinearCycle n power →
  CPnRationalLinearCycle n power
addLinearCycle (linearCycle left) (linearCycle right) =
  linearCycle (left + right)

scaleLinearCycle :
  ∀ {n power} →
  ℚ →
  CPnRationalLinearCycle n power →
  CPnRationalLinearCycle n power
scaleLinearCycle scalar (linearCycle coefficient) =
  linearCycle (scalar * coefficient)

zeroHodgeClass :
  ∀ {n power} → CPnRationalHodgeClass n power
zeroHodgeClass = hodgeClass 0ℚ

addHodgeClass :
  ∀ {n power} →
  CPnRationalHodgeClass n power →
  CPnRationalHodgeClass n power →
  CPnRationalHodgeClass n power
addHodgeClass (hodgeClass left) (hodgeClass right) =
  hodgeClass (left + right)

scaleHodgeClass :
  ∀ {n power} →
  ℚ →
  CPnRationalHodgeClass n power →
  CPnRationalHodgeClass n power
scaleHodgeClass scalar (hodgeClass coefficient) =
  hodgeClass (scalar * coefficient)

linearCycleClass :
  ∀ {n power} →
  CPnRationalLinearCycle n power →
  CPnRationalHodgeClass n power
linearCycleClass (linearCycle coefficient) =
  hodgeClass coefficient

linearCycleClassZero :
  ∀ {n power} →
  linearCycleClass (zeroLinearCycle {n} {power})
  ≡ zeroHodgeClass
linearCycleClassZero = refl

linearCycleClassAdditive :
  ∀ {n power}
    (left right : CPnRationalLinearCycle n power) →
  linearCycleClass (addLinearCycle left right)
  ≡ addHodgeClass
      (linearCycleClass left)
      (linearCycleClass right)
linearCycleClassAdditive (linearCycle left) (linearCycle right) = refl

linearCycleClassHomogeneous :
  ∀ {n power}
    (scalar : ℚ)
    (cycle : CPnRationalLinearCycle n power) →
  linearCycleClass (scaleLinearCycle scalar cycle)
  ≡ scaleHodgeClass scalar (linearCycleClass cycle)
linearCycleClassHomogeneous scalar (linearCycle coefficient) = refl

linearCycleRepresentingClass :
  ∀ {n power} →
  CPnRationalHodgeClass n power →
  CPnRationalLinearCycle n power
linearCycleRepresentingClass (hodgeClass coefficient) =
  linearCycle coefficient

linearCycleClassSurjective :
  ∀ {n power}
    (h : CPnRationalHodgeClass n power) →
  linearCycleClass (linearCycleRepresentingClass h) ≡ h
linearCycleClassSurjective (hodgeClass coefficient) = refl

coordinateLinearSubspace :
  ∀ {n} (power : Basis.ProjectiveSpaceHodgeBasis n) →
  CPnRationalLinearCycle n power
coordinateLinearSubspace power = linearCycle 1ℚ

coordinateLinearSubspaceClassIsHyperplanePower :
  ∀ {n} (power : Basis.ProjectiveSpaceHodgeBasis n) →
  linearCycleClass (coordinateLinearSubspace power)
  ≡ hodgeClass 1ℚ
coordinateLinearSubspaceClassIsHyperplanePower power = refl

rationalMultipleOfLinearSubspaceRepresents :
  ∀ {n} (power : Basis.ProjectiveSpaceHodgeBasis n)
    (coefficient : ℚ) →
  linearCycleClass
    (scaleLinearCycle coefficient
      (coordinateLinearSubspace power))
  ≡ hodgeClass coefficient
rationalMultipleOfLinearSubspaceRepresents power coefficient =
  hodgeClassExt (solve (coefficient ∷ []))
  where
    hodgeClassExt :
      ∀ {n power}
        {left right : CPnRationalHodgeClass n power} →
      hodgeCoefficient left ≡ hodgeCoefficient right →
      left ≡ right
    hodgeClassExt {left = hodgeClass _} {right = hodgeClass _} refl = refl

record AlgebraicRepresentative
    {n : Nat}
    (power : Basis.ProjectiveSpaceHodgeBasis n)
    (h : CPnRationalHodgeClass n power) : Set where
  field
    cycle : CPnRationalLinearCycle n power
    represents : linearCycleClass cycle ≡ h

open AlgebraicRepresentative public

everyFiniteCPnHodgeBasisClassIsAlgebraic :
  ∀ {n} (power : Basis.ProjectiveSpaceHodgeBasis n)
    (h : CPnRationalHodgeClass n power) →
  AlgebraicRepresentative power h
everyFiniteCPnHodgeBasisClassIsAlgebraic power h = record
  { cycle = linearCycleRepresentingClass h
  ; represents = linearCycleClassSurjective h
  }
