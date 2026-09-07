module DASHI.Physics.RootSystemB4WeylAction where

open import Data.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (ℤ)
open import Data.Integer using (-_)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.Vec using (Vec; []; _∷_)

open import DASHI.Physics.RootSystemB4Carrier as B4 using (B4Point)

concatW : ∀ {A : Set} → List (List A) → List A
concatW [] = []
concatW (xs ∷ xss) = xs ++ concatW xss
  where
    _++_ : ∀ {A : Set} → List A → List A → List A
    [] ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

concatMapW : ∀ {A B : Set} → (A → List B) → List A → List B
concatMapW f xs = concatW (map f xs)

data Perm4 : Set where
  p0123 : Perm4
  p0132 : Perm4
  p0213 : Perm4
  p0231 : Perm4
  p0312 : Perm4
  p0321 : Perm4
  p1023 p1032 p1203 p1230 p1302 p1320 : Perm4
  p2013 p2031 p2103 p2130 p2301 p2310 : Perm4
  p3012 p3021 p3102 p3120 p3201 p3210 : Perm4

permute4 : Perm4 → B4.B4Point → B4.B4Point
permute4 p (a ∷ b ∷ c ∷ d ∷ []) with p
... | p0123 = a ∷ b ∷ c ∷ d ∷ []
... | p0132 = a ∷ b ∷ d ∷ c ∷ []
... | p0213 = a ∷ c ∷ b ∷ d ∷ []
... | p0231 = a ∷ c ∷ d ∷ b ∷ []
... | p0312 = a ∷ d ∷ b ∷ c ∷ []
... | p0321 = a ∷ d ∷ c ∷ b ∷ []
... | p1023 = b ∷ a ∷ c ∷ d ∷ []
... | p1032 = b ∷ a ∷ d ∷ c ∷ []
... | p1203 = b ∷ c ∷ a ∷ d ∷ []
... | p1230 = b ∷ c ∷ d ∷ a ∷ []
... | p1302 = b ∷ d ∷ a ∷ c ∷ []
... | p1320 = b ∷ d ∷ c ∷ a ∷ []
... | p2013 = c ∷ a ∷ b ∷ d ∷ []
... | p2031 = c ∷ a ∷ d ∷ b ∷ []
... | p2103 = c ∷ b ∷ a ∷ d ∷ []
... | p2130 = c ∷ b ∷ d ∷ a ∷ []
... | p2301 = c ∷ d ∷ a ∷ b ∷ []
... | p2310 = c ∷ d ∷ b ∷ a ∷ []
... | p3012 = d ∷ a ∷ b ∷ c ∷ []
... | p3021 = d ∷ a ∷ c ∷ b ∷ []
... | p3102 = d ∷ b ∷ a ∷ c ∷ []
... | p3120 = d ∷ b ∷ c ∷ a ∷ []
... | p3201 = d ∷ c ∷ a ∷ b ∷ []
... | p3210 = d ∷ c ∷ b ∷ a ∷ []

allPerm4 : List Perm4
allPerm4 =
  p0123 ∷ p0132 ∷ p0213 ∷ p0231 ∷ p0312 ∷ p0321 ∷
  p1023 ∷ p1032 ∷ p1203 ∷ p1230 ∷ p1302 ∷ p1320 ∷
  p2013 ∷ p2031 ∷ p2103 ∷ p2130 ∷ p2301 ∷ p2310 ∷
  p3012 ∷ p3021 ∷ p3102 ∷ p3120 ∷ p3201 ∷ p3210 ∷
  []

flipInt : Bool → ℤ → ℤ
flipInt true x = x
flipInt false x = - x

flipBy4 : Vec Bool 4 → B4.B4Point → B4.B4Point
flipBy4 (f1 ∷ f2 ∷ f3 ∷ f4 ∷ []) (a ∷ b ∷ c ∷ d ∷ []) =
  flipInt f1 a ∷
  flipInt f2 b ∷
  flipInt f3 c ∷
  flipInt f4 d ∷
  []

record WeylB4 : Set where
  field
    perm : Perm4
    flips : Vec Bool 4

open WeylB4 public

actWeyl : WeylB4 → B4.B4Point → B4.B4Point
actWeyl w x = flipBy4 (flips w) (permute4 (perm w) x)

allBool : List Bool
allBool = false ∷ true ∷ []

allVecBool : ∀ (n : Nat) → List (Vec Bool n)
allVecBool zero = [] ∷ []
allVecBool (suc n) =
  concatMapW
    (λ b → map (λ v → b ∷ v) (allVecBool n))
    allBool

allWeylB4 : List WeylB4
allWeylB4 =
  concatMapW
    (λ p → map (λ fs → record { perm = p ; flips = fs }) (allVecBool 4))
    allPerm4
