module DASHI.Moonshine.Monster3BFiniteSchrodingerProjector729Exact where

------------------------------------------------------------------------
-- SIX CHARACTER PROJECTORS PRODUCE THE EXACT 3^6 = 729 SCALAR
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BCyclotomicLinearAlgebraExact as L
import DASHI.Moonshine.Monster3BFiniteSchrodingerPointProjectorEvaluationExact as Eval

3ℚ : ℚ
3ℚ = 1ℚ + (1ℚ + 1ℚ)

729ℚ : ℚ
729ℚ = _*_ 3ℚ (_*_ 3ℚ (_*_ 3ℚ (_*_ 3ℚ (_*_ 3ℚ 3ℚ))))

tripleIsScaleThree : (a : C3.Cyclotomic3) → Eval.triple a ≡ L.scale 3ℚ a
tripleIsScaleThree (C3.cyclotomic3 a b) = C3.cyclotomic3Ext stepA stepB
  where
    stepA : a + (a + a) ≡ _*_ 3ℚ a
    stepA = solve (a ∷ [])

    stepB : b + (b + b) ≡ _*_ 3ℚ b
    stepB = solve (b ∷ [])

sixTriplesAre729 : (a : C3.Cyclotomic3) →
  Eval.triple6 a ≡ L.scale 729ℚ a
sixTriplesAre729 a =
  trans (cong Eval.triple t5)
    (trans (tripleIsScaleThree (L.scale (_*_ 3ℚ (_*_ 3ℚ (_*_ 3ℚ (_*_ 3ℚ 3ℚ)))) a))
      (L.scaleScale 3ℚ (_*_ 3ℚ (_*_ 3ℚ (_*_ 3ℚ (_*_ 3ℚ 3ℚ)))) a))
  where
    t1 : Eval.triple a ≡ L.scale 3ℚ a
    t1 = tripleIsScaleThree a

    t2 : Eval.triple2 a ≡ L.scale (_*_ 3ℚ 3ℚ) a
    t2 = trans (cong Eval.triple t1)
           (trans (tripleIsScaleThree (L.scale 3ℚ a))
             (L.scaleScale 3ℚ 3ℚ a))

    t3 : Eval.triple3 a ≡ L.scale (_*_ 3ℚ (_*_ 3ℚ 3ℚ)) a
    t3 = trans (cong Eval.triple t2)
           (trans (tripleIsScaleThree (L.scale (_*_ 3ℚ 3ℚ) a))
             (L.scaleScale 3ℚ (_*_ 3ℚ 3ℚ) a))

    t4 : Eval.triple4 a ≡ L.scale (_*_ 3ℚ (_*_ 3ℚ (_*_ 3ℚ 3ℚ))) a
    t4 = trans (cong Eval.triple t3)
           (trans (tripleIsScaleThree (L.scale (_*_ 3ℚ (_*_ 3ℚ 3ℚ)) a))
             (L.scaleScale 3ℚ (_*_ 3ℚ (_*_ 3ℚ 3ℚ)) a))

    t5 : Eval.triple5 a ≡ L.scale (_*_ 3ℚ (_*_ 3ℚ (_*_ 3ℚ (_*_ 3ℚ 3ℚ)))) a
    t5 = trans (cong Eval.triple t4)
           (trans (tripleIsScaleThree (L.scale (_*_ 3ℚ (_*_ 3ℚ (_*_ 3ℚ 3ℚ))) a))
             (L.scaleScale 3ℚ (_*_ 3ℚ (_*_ 3ℚ (_*_ 3ℚ 3ℚ))) a))

record Projector729Boundary : Set where
  constructor projector729Boundary
  field
    sixCoordinateProjectorScaleIs729 : Bool
open Projector729Boundary public

canonicalProjector729Boundary : Projector729Boundary
canonicalProjector729Boundary = projector729Boundary true
