module Ontology.GodelLattice where

open import Agda.Builtin.Nat      using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.List     using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Nullary.Decidable.Core using (yes; no)

open import MonsterOntos

------------------------------------------------------------------------
-- A factor-exponent vector over the 15 primes is a canonical coordinate.

record Vec15 (A : Set) : Set where
  constructor v15
  field
    e2  : A; e3  : A; e5  : A; e7  : A; e11 : A
    e13 : A; e17 : A; e19 : A; e23 : A; e29 : A
    e31 : A; e41 : A; e47 : A; e59 : A; e71 : A

Exponent : Set
Exponent = Nat

FactorVec : Set
FactorVec = Vec15 Exponent

------------------------------------------------------------------------
-- Prime-indexed updates on Vec15.

updateField :
  {A : Set} →
  SSP →
  SSP →
  (A → A) →
  A →
  A
updateField p lane f x with p ≟ lane
... | yes _ = f x
... | no _  = x

updateVec15 :
  {A : Set} →
  SSP →
  (A → A) →
  Vec15 A →
  Vec15 A
updateVec15 p f (v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  v15
    (updateField p p2 f e2)
    (updateField p p3 f e3)
    (updateField p p5 f e5)
    (updateField p p7 f e7)
    (updateField p p11 f e11)
    (updateField p p13 f e13)
    (updateField p p17 f e17)
    (updateField p p19 f e19)
    (updateField p p23 f e23)
    (updateField p p29 f e29)
    (updateField p p31 f e31)
    (updateField p p41 f e41)
    (updateField p p47 f e47)
    (updateField p p59 f e59)
    (updateField p p71 f e71)

updateField-commutes :
  {A : Set} →
  (p q lane : SSP) →
  (f g : A → A) →
  ((x : A) → f (g x) ≡ g (f x)) →
  (x : A) →
  updateField p lane f (updateField q lane g x)
    ≡
  updateField q lane g (updateField p lane f x)
updateField-commutes p q lane f g fg x with p ≟ lane | q ≟ lane
... | yes _ | yes _ = fg x
... | yes _ | no _  = refl
... | no _  | yes _ = refl
... | no _  | no _  = refl

updateVec15-commutes :
  {A : Set} →
  (p q : SSP) →
  (f g : A → A) →
  ((x : A) → f (g x) ≡ g (f x)) →
  (v : Vec15 A) →
  updateVec15 p f (updateVec15 q g v)
    ≡
  updateVec15 q g (updateVec15 p f v)
updateVec15-commutes p q f g fg
  (v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71)
  rewrite updateField-commutes p q p2 f g fg e2
        | updateField-commutes p q p3 f g fg e3
        | updateField-commutes p q p5 f g fg e5
        | updateField-commutes p q p7 f g fg e7
        | updateField-commutes p q p11 f g fg e11
        | updateField-commutes p q p13 f g fg e13
        | updateField-commutes p q p17 f g fg e17
        | updateField-commutes p q p19 f g fg e19
        | updateField-commutes p q p23 f g fg e23
        | updateField-commutes p q p29 f g fg e29
        | updateField-commutes p q p31 f g fg e31
        | updateField-commutes p q p41 f g fg e41
        | updateField-commutes p q p47 f g fg e47
        | updateField-commutes p q p59 f g fg e59
        | updateField-commutes p q p71 f g fg e71
  = refl

------------------------------------------------------------------------
-- Abstract "text" (you’ll plug a real representation later)

postulate
  Text : Set

------------------------------------------------------------------------
-- Gödel encoding contract:
-- encode gives a Nat; factorMap gives exponents over SSP primes.
-- The key property is that factorMap is a homomorphism for concatenation
-- (or some composition), if you want that. Here we keep it minimal.

postulate
  encode   : Text → Nat
  factorMap : Text → FactorVec

------------------------------------------------------------------------
-- Self-verifying coordinate means: equality of factor-vectors is a stable
-- identifier under the chosen equivalence (you decide what that is).
-- We DO NOT claim it is “reality”; we claim it is a canonical coordinate.

record CoordinateLaw : Set₁ where
  field
    stable-id :
      ∀ (t₁ t₂ : Text) →
      factorMap t₁ ≡ factorMap t₂ → encode t₁ ≡ encode t₂
