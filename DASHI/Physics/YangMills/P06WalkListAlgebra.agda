module DASHI.Physics.YangMills.P06WalkListAlgebra where

open import DASHI.Physics.YangMills.GraphCombinatorics
  using (mapList; concatMapList; append-singleton-injective)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Data.Product using (_×_; proj₁; proj₂)

------------------------------------------------------------------------
-- Small list-algebra facts used by the P06 generated-walk encoding.
------------------------------------------------------------------------

mapList-++ :
  {A B : Set} (f : A → B) (xs ys : List A) →
  mapList f (xs ++ ys) ≡ mapList f xs ++ mapList f ys
mapList-++ f [] ys = refl
mapList-++ f (x ∷ xs) ys =
  cong (λ zs → f x ∷ zs) (mapList-++ f xs ys)

mapList-concatMap :
  {A B C : Set} (g : B → C) (f : A → List B) (xs : List A) →
  mapList g (concatMapList f xs) ≡
  concatMapList (λ x → mapList g (f x)) xs
mapList-concatMap g f [] = refl
mapList-concatMap g f (x ∷ xs) =
  trans
    (mapList-++ g (f x) (concatMapList f xs))
    (cong
      (λ zs → mapList g (f x) ++ zs)
      (mapList-concatMap g f xs))

-- The two projections are named here so callers do not need to depend on
-- the snoc implementation used by GraphCombinatorics.
append-singleton-cancel-prefix :
  {A : Set} {xs ys : List A} {x y : A} →
  xs ++ (x ∷ []) ≡ ys ++ (y ∷ []) → xs ≡ ys
append-singleton-cancel-prefix eq = proj₁ (append-singleton-injective eq)

append-singleton-cancel-last :
  {A : Set} {xs ys : List A} {x y : A} →
  xs ++ (x ∷ []) ≡ ys ++ (y ∷ []) → x ≡ y
append-singleton-cancel-last eq = proj₂ (append-singleton-injective eq)
