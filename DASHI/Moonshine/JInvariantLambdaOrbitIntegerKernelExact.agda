module DASHI.Moonshine.JInvariantLambdaOrbitIntegerKernelExact where

-- Classical Legendre j; reuse the original Base369 orbit labels.
-- Homogeneous integer coordinates a/b avoid partial division.
-- Numerator and denominator are individually invariant, not merely
-- cross-multiplication equal. Analytic lambda(tau) is not defined here.
-- Prior owner: JInvariantLambdaOrbitBase369BridgeExact.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; _+_; _-_; _*_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Base369 using (HexTruth)
open import DASHI.Moonshine.JInvariantLambdaOrbitBase369BridgeExact
  using (LambdaOrbitTag; lambdaIdentity; lambdaOneOverOneMinus;
         lambdaMinusOneOverLambda; lambdaReciprocal;
         lambdaOverLambdaMinusOne; lambdaOneMinus; hexToLambdaOrbit)

record Homogeneous : Set where
  constructor pair
  field
    a b : ℤ
open Homogeneous public

orbit : LambdaOrbitTag → Homogeneous → Homogeneous
orbit lambdaIdentity (pair a b) = pair a b
orbit lambdaOneOverOneMinus (pair a b) = pair b (b - a)
orbit lambdaMinusOneOverLambda (pair a b) = pair (a - b) a
orbit lambdaReciprocal (pair a b) = pair b a
orbit lambdaOverLambdaMinusOne (pair a b) = pair a (a - b)
orbit lambdaOneMinus (pair a b) = pair (b - a) b

quadratic : Homogeneous → ℤ
quadratic (pair a b) = a * a - a * b + b * b

denominator : Homogeneous → ℤ
denominator (pair a b) = (a * b * (b - a)) * (a * b * (b - a))

numerator : Homogeneous → ℤ
numerator x = (+ 256) * quadratic x * quadratic x * quadratic x

quadraticInvariant : (t : LambdaOrbitTag) (x : Homogeneous) →
  quadratic (orbit t x) ≡ quadratic x
quadraticInvariant lambdaIdentity (pair a b) =
  solve 2 (λ a b → (a :* a :- a :* b :+ b :* b) := (a :* a :- a :* b :+ b :* b)) refl a b
quadraticInvariant lambdaOneOverOneMinus (pair a b) =
  solve 2 (λ a b → (b :* b :- b :* (b :- a) :+ (b :- a) :* (b :- a)) := (a :* a :- a :* b :+ b :* b)) refl a b
quadraticInvariant lambdaMinusOneOverLambda (pair a b) =
  solve 2 (λ a b → ((a :- b) :* (a :- b) :- (a :- b) :* a :+ a :* a) := (a :* a :- a :* b :+ b :* b)) refl a b
quadraticInvariant lambdaReciprocal (pair a b) =
  solve 2 (λ a b → (b :* b :- b :* a :+ a :* a) := (a :* a :- a :* b :+ b :* b)) refl a b
quadraticInvariant lambdaOverLambdaMinusOne (pair a b) =
  solve 2 (λ a b → (a :* a :- a :* (a :- b) :+ (a :- b) :* (a :- b)) := (a :* a :- a :* b :+ b :* b)) refl a b
quadraticInvariant lambdaOneMinus (pair a b) =
  solve 2 (λ a b → ((b :- a) :* (b :- a) :- (b :- a) :* b :+ b :* b) := (a :* a :- a :* b :+ b :* b)) refl a b

denominatorInvariant : (t : LambdaOrbitTag) (x : Homogeneous) →
  denominator (orbit t x) ≡ denominator x
denominatorInvariant lambdaIdentity (pair a b) =
  solve 2 (λ a b → ((a :* b :* (b :- a)) :* (a :* b :* (b :- a))) := ((a :* b :* (b :- a)) :* (a :* b :* (b :- a)))) refl a b
denominatorInvariant lambdaOneOverOneMinus (pair a b) =
  solve 2 (λ a b → ((b :* (b :- a) :* ((b :- a) :- b)) :* (b :* (b :- a) :* ((b :- a) :- b))) := ((a :* b :* (b :- a)) :* (a :* b :* (b :- a)))) refl a b
denominatorInvariant lambdaMinusOneOverLambda (pair a b) =
  solve 2 (λ a b → (((a :- b) :* a :* (a :- (a :- b))) :* ((a :- b) :* a :* (a :- (a :- b)))) := ((a :* b :* (b :- a)) :* (a :* b :* (b :- a)))) refl a b
denominatorInvariant lambdaReciprocal (pair a b) =
  solve 2 (λ a b → ((b :* a :* (a :- b)) :* (b :* a :* (a :- b))) := ((a :* b :* (b :- a)) :* (a :* b :* (b :- a)))) refl a b
denominatorInvariant lambdaOverLambdaMinusOne (pair a b) =
  solve 2 (λ a b → ((a :* (a :- b) :* ((a :- b) :- a)) :* (a :* (a :- b) :* ((a :- b) :- a))) := ((a :* b :* (b :- a)) :* (a :* b :* (b :- a)))) refl a b
denominatorInvariant lambdaOneMinus (pair a b) =
  solve 2 (λ a b → (((b :- a) :* b :* (b :- (b :- a))) :* ((b :- a) :* b :* (b :- (b :- a)))) := ((a :* b :* (b :- a)) :* (a :* b :* (b :- a)))) refl a b

numeratorInvariant : (t : LambdaOrbitTag) (x : Homogeneous) →
  numerator (orbit t x) ≡ numerator x
numeratorInvariant t x rewrite quadraticInvariant t x = refl

-- A nonzero denominator witness is transported without re-proving
-- six separate apartness results. The concrete rational quotient is
-- not totalised or evaluated at the singular coordinates.
open import Data.Empty using (⊥)
open import Data.Integer using (0ℤ)
nonzeroTransport : (t : LambdaOrbitTag) (x : Homogeneous) →
  (denominator x ≡ 0ℤ → ⊥) →
  denominator (orbit t x) ≡ 0ℤ → ⊥
nonzeroTransport t x nz rewrite denominatorInvariant t x = nz

hexNumeratorInvariant : (h : HexTruth) (x : Homogeneous) →
  numerator (orbit (hexToLambdaOrbit h) x) ≡ numerator x
hexNumeratorInvariant h = numeratorInvariant (hexToLambdaOrbit h)

hexDenominatorInvariant : (h : HexTruth) (x : Homogeneous) →
  denominator (orbit (hexToLambdaOrbit h) x) ≡ denominator x
hexDenominatorInvariant h = denominatorInvariant (hexToLambdaOrbit h)

-- Source-written ring proofs; pinned Agda acceptance still required.
-- No analytic modular lambda or Monster character identity is asserted.
