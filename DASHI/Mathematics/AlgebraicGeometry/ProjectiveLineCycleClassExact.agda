module DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineCycleClassExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Claire Voisin,
-- "Hodge Theory and Complex Algebraic Geometry I".
-- DOI: 10.1017/CBO9780511615344.
--
-- Pierre Deligne,
-- "The Hodge Conjecture", Clay Mathematics Institute problem description.
-- No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Give a concrete codimension-one cycle-class model for the projective line.
-- Rational divisor cycles and rational H^(1,1)-classes are both represented by
-- ℚ; the cycle-class map is the identity.  Linearity and surjectivity are
-- therefore proved exactly, and the class 1 is represented by the point-cycle
-- generator.
--
-- This closes the finite P^1 example only.  Identifying the model with the
-- singular/de Rham cohomology of a constructed smooth projective variety and
-- proving the Hodge conjecture in higher dimensions remain separate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

record P1RationalDivisorCycle : Set where
  constructor divisorCycle
  field
    divisorCoefficient : ℚ

open P1RationalDivisorCycle public

record P1RationalH11Class : Set where
  constructor h11Class
  field
    h11Coefficient : ℚ

open P1RationalH11Class public

zeroDivisorCycle : P1RationalDivisorCycle
zeroDivisorCycle = divisorCycle 0ℚ

addDivisorCycle :
  P1RationalDivisorCycle → P1RationalDivisorCycle → P1RationalDivisorCycle
addDivisorCycle (divisorCycle left) (divisorCycle right) =
  divisorCycle (left + right)

scaleDivisorCycle : ℚ → P1RationalDivisorCycle → P1RationalDivisorCycle
scaleDivisorCycle scalar (divisorCycle coefficient) =
  divisorCycle (scalar * coefficient)

zeroH11Class : P1RationalH11Class
zeroH11Class = h11Class 0ℚ

addH11Class : P1RationalH11Class → P1RationalH11Class → P1RationalH11Class
addH11Class (h11Class left) (h11Class right) =
  h11Class (left + right)

scaleH11Class : ℚ → P1RationalH11Class → P1RationalH11Class
scaleH11Class scalar (h11Class coefficient) =
  h11Class (scalar * coefficient)

p1CycleClass : P1RationalDivisorCycle → P1RationalH11Class
p1CycleClass (divisorCycle coefficient) = h11Class coefficient

p1CycleClassZero :
  p1CycleClass zeroDivisorCycle ≡ zeroH11Class
p1CycleClassZero = refl

p1CycleClassAdditive : ∀ left right →
  p1CycleClass (addDivisorCycle left right)
  ≡ addH11Class (p1CycleClass left) (p1CycleClass right)
p1CycleClassAdditive (divisorCycle left) (divisorCycle right) = refl

p1CycleClassHomogeneous : ∀ scalar cycle →
  p1CycleClass (scaleDivisorCycle scalar cycle)
  ≡ scaleH11Class scalar (p1CycleClass cycle)
p1CycleClassHomogeneous scalar (divisorCycle coefficient) = refl

cycleRepresentingH11Class : P1RationalH11Class → P1RationalDivisorCycle
cycleRepresentingH11Class (h11Class coefficient) = divisorCycle coefficient

p1CycleClassSurjective : ∀ hodgeClass →
  p1CycleClass (cycleRepresentingH11Class hodgeClass) ≡ hodgeClass
p1CycleClassSurjective (h11Class coefficient) = refl

pointCycle : P1RationalDivisorCycle
pointCycle = divisorCycle 1ℚ

pointCycleClassIsGenerator :
  p1CycleClass pointCycle ≡ h11Class 1ℚ
pointCycleClassIsGenerator = refl

rationalMultipleOfPointRepresentsClass : ∀ coefficient →
  p1CycleClass (scaleDivisorCycle coefficient pointCycle)
  ≡ h11Class coefficient
rationalMultipleOfPointRepresentsClass coefficient =
  h11Ext (solve (coefficient ∷ []))
  where
    h11Ext : ∀ {left right} →
      h11Coefficient left ≡ h11Coefficient right → left ≡ right
    h11Ext {h11Class _} {h11Class _} refl = refl

record P1CycleClassCertificate : Set where
  field
    linearZero : p1CycleClass zeroDivisorCycle ≡ zeroH11Class
    linearAdd : ∀ left right →
      p1CycleClass (addDivisorCycle left right)
      ≡ addH11Class (p1CycleClass left) (p1CycleClass right)
    linearScale : ∀ scalar cycle →
      p1CycleClass (scaleDivisorCycle scalar cycle)
      ≡ scaleH11Class scalar (p1CycleClass cycle)
    everyH11ClassHasCycle : ∀ hodgeClass →
      p1CycleClass (cycleRepresentingH11Class hodgeClass) ≡ hodgeClass

p1CycleClassCertificate : P1CycleClassCertificate
p1CycleClassCertificate = record
  { linearZero = p1CycleClassZero
  ; linearAdd = p1CycleClassAdditive
  ; linearScale = p1CycleClassHomogeneous
  ; everyH11ClassHasCycle = p1CycleClassSurjective
  }
