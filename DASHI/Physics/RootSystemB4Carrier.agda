module DASHI.Physics.RootSystemB4Carrier where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (Dec; yes; no)

open import Data.Integer.Base using (ℤ; +_)
open import Data.Integer using (_≟_; -_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Vec using (Vec; []; _∷_; head; tail)

B4Point : Set
B4Point = Vec ℤ 4

pt : ℤ → ℤ → ℤ → ℤ → B4Point
pt a b c d = a ∷ b ∷ c ∷ d ∷ []

z : ℤ
z = + 0

p1 : ℤ
p1 = + 1

n1 : ℤ
n1 = - (+ 1)

decEqInt : (x y : ℤ) → Dec (x ≡ y)
decEqInt x y with x ≟ y
... | yes refl = yes refl
... | no neq = no neq

decEqB4Point : (x y : B4Point) → Dec (x ≡ y)
decEqB4Point (a1 ∷ a2 ∷ a3 ∷ a4 ∷ []) (b1 ∷ b2 ∷ b3 ∷ b4 ∷ [])
  with decEqInt a1 b1
... | no neq = no (λ eq → neq (cong head eq))
... | yes refl with decEqInt a2 b2
... | no neq = no (λ eq → neq (cong head (cong tail eq)))
... | yes refl with decEqInt a3 b3
... | no neq = no (λ eq → neq (cong head (cong tail (cong tail eq))))
... | yes refl with decEqInt a4 b4
... | no neq = no (λ eq → neq (cong head (cong tail (cong tail (cong tail eq)))))
... | yes refl = yes refl

pair12 : ℤ → ℤ → B4Point
pair12 a b = pt a b z z

pair13 : ℤ → ℤ → B4Point
pair13 a b = pt a z b z

pair14 : ℤ → ℤ → B4Point
pair14 a b = pt a z z b

pair23 : ℤ → ℤ → B4Point
pair23 a b = pt z a b z

pair24 : ℤ → ℤ → B4Point
pair24 a b = pt z a z b

pair34 : ℤ → ℤ → B4Point
pair34 a b = pt z z a b

concat : ∀ {A : Set} → List (List A) → List A
concat [] = []
concat (xs ∷ xss) = xs ++ concat xss
  where
    _++_ : ∀ {A : Set} → List A → List A → List A
    [] ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

signedVariants : (ℤ → ℤ → B4Point) → List B4Point
signedVariants mk =
  mk p1 p1 ∷
  mk p1 n1 ∷
  mk n1 p1 ∷
  mk n1 n1 ∷
  []

shell1Points : List B4Point
shell1Points =
  pt p1 z z z ∷
  pt n1 z z z ∷
  pt z p1 z z ∷
  pt z n1 z z ∷
  pt z z p1 z ∷
  pt z z n1 z ∷
  pt z z z p1 ∷
  pt z z z n1 ∷
  []

shell2Points : List B4Point
shell2Points =
  concat
    ( signedVariants pair12 ∷
      signedVariants pair13 ∷
      signedVariants pair14 ∷
      signedVariants pair23 ∷
      signedVariants pair24 ∷
      signedVariants pair34 ∷
      []
    )
