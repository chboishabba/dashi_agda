module DASHI.Physics.YangMills.BalabanQuadraticListExpansionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (sq; sumQ; twoℚ)

------------------------------------------------------------------------
-- A tiny degree-two compiler for rational linear forms.
--
-- Ring reflection is used only on the two/three-scalar algebra laws below.
-- Arbitrarily long linear forms are expanded structurally by List recursion,
-- so a 12-coordinate square never enters the generic RingSolver as one dense
-- multivariate product.
------------------------------------------------------------------------

crossWith : ℚ → List ℚ → ℚ
crossWith x [] = 0ℚ
crossWith x (y ∷ ys) = twoℚ * x * y + crossWith x ys

squareExpansion : List ℚ → ℚ
squareExpansion [] = 0ℚ
squareExpansion (x ∷ xs) =
  sq x + (crossWith x xs + squareExpansion xs)

crossStepRaw : ∀ x y z →
  twoℚ * x * y + twoℚ * x * z
  ≡ twoℚ * x * (y + z)
crossStepRaw = ℚRing.solve-∀

crossWithSum : ∀ x xs →
  crossWith x xs ≡ twoℚ * x * sumQ xs
crossWithSum x [] = ℚRing.solve-∀
crossWithSum x (y ∷ ys)
  rewrite crossWithSum x ys
  = crossStepRaw x y (sumQ ys)

squareStepRaw : ∀ x s →
  sq (x + s)
  ≡ sq x + (twoℚ * x * s + sq s)
squareStepRaw = ℚRing.solve-∀

squareSumExpansion : ∀ xs →
  sq (sumQ xs) ≡ squareExpansion xs
squareSumExpansion [] = ℚRing.solve-∀
squareSumExpansion (x ∷ xs)
  rewrite crossWithSum x xs
        | sym (squareSumExpansion xs)
  = squareStepRaw x (sumQ xs)
