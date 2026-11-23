module DASHI.Moonshine.Monster3BFiniteSchrodingerProjector729Exact where

------------------------------------------------------------------------
-- SIX CHARACTER PROJECTORS PRODUCE THE EXACT 3^6 = 729 SCALAR
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BCyclotomicLinearAlgebraExact as L
import DASHI.Moonshine.Monster3BFiniteSchrodingerPointProjectorEvaluationExact as Eval

729ℚ : ℚ
729ℚ = + 729 / 1

c1 : ℚ
c1 = 1ℚ

c2 : ℚ
c2 = c1 + (c1 + c1)

c3 : ℚ
c3 = c2 + (c2 + c2)

c4 : ℚ
c4 = c3 + (c3 + c3)

c5 : ℚ
c5 = c4 + (c4 + c4)

c6 : ℚ
c6 = c5 + (c5 + c5)

c7 : ℚ
c7 = c6 + (c6 + c6)

c7Is729 : c7 ≡ 729ℚ
c7Is729 = refl

t : ℚ → ℚ
t x = x + (x + x)

distrib3 : (c x : ℚ) → (c * x) + ((c * x) + (c * x)) ≡ (c + (c + c)) * x
distrib3 c x = solve (c ∷ x ∷ [])

step : (c x : ℚ) → t (c * x) ≡ (c + (c + c)) * x
step c x = distrib3 c x

step0 : (x : ℚ) → x ≡ c1 * x
step0 x = solve (x ∷ [])

t6 : (x : ℚ) → t (t (t (t (t (t x))))) ≡ 729ℚ * x
t6 x =
  trans (cong (λ y → t (t (t (t (t y))))) (trans (cong t (step0 x)) (step c1 x)))
  (trans (cong (λ y → t (t (t (t y)))) (step c2 x))
  (trans (cong (λ y → t (t (t y))) (step c3 x))
  (trans (cong (λ y → t (t y)) (step c4 x))
  (trans (cong (λ y → t y) (step c5 x))
  (trans (step c6 x) (cong (λ k → k * x) c7Is729))))))

sixTriplesAre729 : (a : C3.Cyclotomic3) →
  Eval.triple6 a ≡ L.scale 729ℚ a
sixTriplesAre729 (C3.cyclotomic3 a b) =
  C3.cyclotomic3Ext (t6 a) (t6 b)

record Projector729Boundary : Set where
  constructor projector729Boundary
  field
    sixCoordinateProjectorScaleIs729 : Bool
open Projector729Boundary public

canonicalProjector729Boundary : Projector729Boundary
canonicalProjector729Boundary = projector729Boundary true
