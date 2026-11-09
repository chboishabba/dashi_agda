module DASHI.Foundations.AffineProductIdentifiabilityExact where

-- A reusable finite identifiability theorem. No ecological assumptions.
-- A function of TWO inputs cannot admit a total decoder of either input
-- if a collision changes that input. In particular, affine functions
-- depending solely on the product have such collisions.
-- The theorem is about OUTPUT IDENTIFIABILITY, NOT intent or optimiser use.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

symEq : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
symEq refl = refl

transEq : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transEq refl q = q

congEq : ∀ {A B : Set} (f : A → B) {x y : A} →
         x ≡ y → f x ≡ f y
congEq f refl = refl

-- Generic, domain-independent inverse obstruction.
noLeftDecoderAtCollision :
  ∀ {A B O : Set} (f : A → B → O)
    {a a′ : A} {b b′ : B} →
  f a b ≡ f a′ b′ →
  (a ≡ a′ → ⊥) →
  (decode : O → A) →
  ((x : A) (y : B) → decode (f x y) ≡ x) → ⊥
noLeftDecoderAtCollision f {a = a} {a′ = a′} {b = b} {b′ = b′}
  same distinct decode correct =
  distinct
    (transEq (symEq (correct a b))
      (transEq (congEq decode same) (correct a′ b′)))

noRightDecoderAtCollision :
  ∀ {A B O : Set} (f : A → B → O)
    {a a′ : A} {b b′ : B} →
  f a b ≡ f a′ b′ →
  (b ≡ b′ → ⊥) →
  (decode : O → B) →
  ((x : A) (y : B) → decode (f x y) ≡ y) → ⊥
noRightDecoderAtCollision f {a = a} {a′ = a′} {b = b} {b′ = b′}
  same distinct decode correct =
  distinct
    (transEq (symEq (correct _ _))
      (transEq (congEq decode same) (correct _ _)))

-- Specialisation to an arbitrary affine product coefficient.
-- The coefficient a and scale b are not specific to the OAG.
affineProduct : Nat → Nat → Nat → Nat → Nat
affineProduct a b x y = a + b * (x * y)

sameProductSameAffine :
  (a b x y u v : Nat) →
  x * y ≡ u * v →
  affineProduct a b x y ≡ affineProduct a b u v
sameProductSameAffine a b x y u v equalProduct =
  congEq (λ z → a + b * z) equalProduct

noGainDecoderForAffineProduct :
  (a b x y u v : Nat) →
  x * y ≡ u * v →
  (x ≡ u → ⊥) →
  (decode : Nat → Nat) →
  ((g c : Nat) → decode (affineProduct a b g c) ≡ g) → ⊥
noGainDecoderForAffineProduct a b x y u v same distinct =
  noLeftDecoderAtCollision (affineProduct a b)
    (sameProductSameAffine a b x y u v same) distinct

noConfidenceDecoderForAffineProduct :
  (a b x y u v : Nat) →
  x * y ≡ u * v →
  (y ≡ v → ⊥) →
  (decode : Nat → Nat) →
  ((g c : Nat) → decode (affineProduct a b g c) ≡ c) → ⊥
noConfidenceDecoderForAffineProduct a b x y u v same distinct =
  noRightDecoderAtCollision (affineProduct a b)
    (sameProductSameAffine a b x y u v same) distinct

-- Collision is exact Nat arithmetic; discounting or any downstream
-- deterministic observation function preserves it by congruence.
sameProductSameObservedOutput :
  (a b x y u v : Nat) →
  (observe : Nat → Nat) →
  x * y ≡ u * v →
  observe (affineProduct a b x y) ≡
  observe (affineProduct a b u v)
sameProductSameObservedOutput a b x y u v observe same =
  congEq observe (sameProductSameAffine a b x y u v same)
