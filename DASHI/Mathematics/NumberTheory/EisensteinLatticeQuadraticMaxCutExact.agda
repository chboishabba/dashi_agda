module DASHI.Mathematics.NumberTheory.EisensteinLatticeQuadraticMaxCutExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Integer using (ℤ; +_; _+_; _-_; _*_)
open import Data.Product using (_×_; _,_)
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR

module RingZ = NR IntRS.ring
open RingZ using (Κ; _⊕_; _⊗_; ⊝_; solve)

q : ℤ → ℤ → ℤ
q a b = a * a - a * b + b * b

rotate : ℤ × ℤ → ℤ × ℤ
rotate (a , b) = (a - b , a)

rotateNormInvariant : (a b : ℤ) → q (a - b) a ≡ q a b
rotateNormInvariant a b =
  RingZ.solve 2
    (λ a b →
      (((a ⊝ b) ⊗ (a ⊝ b)) ⊝ ((a ⊝ b) ⊗ a) ⊕ (a ⊗ a)
      , (a ⊗ a) ⊝ (a ⊗ b) ⊕ (b ⊗ b)))
    refl a b

coercivityIdentityA : (a b : ℤ) →
  (+ 4) * q a b ≡ (+ 3) * (a * a) + (a - (+ 2) * b) * (a - (+ 2) * b)
coercivityIdentityA a b =
  RingZ.solve 2
    (λ a b →
      ((Κ (+ 4)) ⊗ ((a ⊗ a) ⊝ (a ⊗ b) ⊕ (b ⊗ b))
      , (Κ (+ 3) ⊗ (a ⊗ a)) ⊕ ((a ⊝ (Κ (+ 2) ⊗ b)) ⊗ (a ⊝ (Κ (+ 2) ⊗ b)))))
    refl a b

coercivityIdentityB : (a b : ℤ) →
  (+ 4) * q a b ≡ (+ 3) * (b * b) + ((+ 2) * a - b) * ((+ 2) * a - b)
coercivityIdentityB a b =
  RingZ.solve 2
    (λ a b →
      ((Κ (+ 4)) ⊗ ((a ⊗ a) ⊝ (a ⊗ b) ⊕ (b ⊗ b))
      , (Κ (+ 3) ⊗ (b ⊗ b)) ⊕ (((Κ (+ 2) ⊗ a) ⊝ b) ⊗ ((Κ (+ 2) ⊗ a) ⊝ b))))
    refl a b

unit1 : q (+ 1) (+ 0) ≡ + 1
unit1 = refl
unit2 : q (+ 0) (+ 1) ≡ + 1
unit2 = refl
unit3 : q (+ 1) (+ 1) ≡ + 1
unit3 = refl

record QuadraticMaxCutBoundary : Set where
  constructor quadratic-max-cut-boundary
  field
    sixfoldRotationNormLawOwned : Bool
    coercivityDecompositionsOwned : Bool
    divisorRepresentationTheoremManufactured : Bool

canonicalQuadraticMaxCutBoundary : QuadraticMaxCutBoundary
canonicalQuadraticMaxCutBoundary = quadratic-max-cut-boundary true true false
