module DASHI.Physics.YangMills.BalabanFiniteRationalOrderCoreExact where

------------------------------------------------------------------------
-- FINITE RATIONAL ORDER CORE
--
-- Small theorem owner below physical/YM consumers.  This module knows only the
-- finite rational fold and rational order.  It provides the preservation fact
-- later registered as a FibreRelationLift; physical energy modules should not
-- own this recursion themselves.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational)

sumRationalMonotone :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  (∀ value → left value ≤ right value) →
  sumRational values left ≤ sumRational values right
sumRationalMonotone [] left right pointwise = ℚP.≤-refl
sumRationalMonotone (value ∷ values) left right pointwise =
  ℚP.+-mono-≤
    (pointwise value)
    (sumRationalMonotone values left right pointwise)
