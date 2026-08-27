module DASHI.Core.ListExact where

open import DASHI.Core.Prelude

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ xs) = 1 + listCount xs

append : ∀ {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

listCountAppend :
  ∀ {A : Set} →
  (xs ys : List A) →
  listCount (append xs ys) ≡ listCount xs + listCount ys
listCountAppend [] ys = refl
listCountAppend (x ∷ xs) ys rewrite listCountAppend xs ys = refl
