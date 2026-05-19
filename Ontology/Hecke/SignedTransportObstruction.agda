module Ontology.Hecke.SignedTransportObstruction where

open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.Nat      using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty            using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)

open import MonsterOntos          using (p2)
open import Ontology.GodelLattice using (FactorVec; Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)
open import Ontology.Hecke.FactorVecInstances using (SupportMask; supportMask)
open import Ontology.Hecke.FactorVecSignedTransport using (transportOrStay)

------------------------------------------------------------------------
-- Concrete obstruction: signed transport does not descend to the coarse
-- support-mask quotient.

SupportMaskRespectsSignedTransport : Set
SupportMaskRespectsSignedTransport =
  ∀ p {x y : FactorVec} →
  supportMask x ≡ supportMask y →
  supportMask (transportOrStay p x) ≡ supportMask (transportOrStay p y)

counterexample-x : FactorVec
counterexample-x =
  mkVec15 (suc zero) zero zero zero zero zero zero zero zero zero zero zero zero zero zero

counterexample-y : FactorVec
counterexample-y =
  mkVec15 (suc (suc zero)) zero zero zero zero zero zero zero zero zero zero zero zero zero zero

counterexample-support :
  supportMask counterexample-x ≡ supportMask counterexample-y
counterexample-support = refl

counterexample-breaks :
  supportMask (transportOrStay p2 counterexample-x)
    ≡
  supportMask (transportOrStay p2 counterexample-y)
    →
  ⊥
counterexample-breaks ()

signedTransport-not-supportMask :
  SupportMaskRespectsSignedTransport → ⊥
signedTransport-not-supportMask respects =
  counterexample-breaks
    (respects p2 {x = counterexample-x} {y = counterexample-y}
      counterexample-support)

------------------------------------------------------------------------
-- Stronger obstruction: no finite positive saturation quotient of the form
-- e ↦ min e K can respect the signed decrement-plus-increment transport.

truncate : Nat → Nat → Nat
truncate zero n = zero
truncate (suc k) zero = zero
truncate (suc k) (suc n) = suc (truncate k n)

truncate-self : ∀ k → truncate k k ≡ k
truncate-self zero = refl
truncate-self (suc k) rewrite truncate-self k = refl

truncate-suc-self : ∀ k → truncate (suc k) (suc (suc k)) ≡ suc k
truncate-suc-self zero = refl
truncate-suc-self (suc k) rewrite truncate-suc-self k = refl

truncate-step-self : ∀ k → truncate (suc k) k ≡ k
truncate-step-self zero = refl
truncate-step-self (suc k) rewrite truncate-step-self k = refl

suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

nat-not-suc-self : ∀ k → k ≡ suc k → ⊥
nat-not-suc-self zero ()
nat-not-suc-self (suc k) eq = nat-not-suc-self k (suc-injective eq)

boundedVec : Nat → FactorVec → FactorVec
boundedVec K (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  mkVec15 (truncate K e2) (truncate K e3) (truncate K e5) (truncate K e7)
          (truncate K e11) (truncate K e13) (truncate K e17) (truncate K e19)
          (truncate K e23) (truncate K e29) (truncate K e31) (truncate K e41)
          (truncate K e47) (truncate K e59) (truncate K e71)

BoundedRespectsSignedTransport : Nat → Set
BoundedRespectsSignedTransport K =
  ∀ p {x y : FactorVec} →
  boundedVec K x ≡ boundedVec K y →
  boundedVec K (transportOrStay p x) ≡ boundedVec K (transportOrStay p y)

bounded-counterexample-x : Nat → FactorVec
bounded-counterexample-x k =
  mkVec15 (suc k) zero zero zero zero zero zero zero zero zero zero zero zero zero zero

bounded-counterexample-y : Nat → FactorVec
bounded-counterexample-y k =
  mkVec15 (suc (suc k)) zero zero zero zero zero zero zero zero zero zero zero zero zero zero

bounded-counterexample-eq :
  ∀ k →
  boundedVec (suc k) (bounded-counterexample-x k)
    ≡
  boundedVec (suc k) (bounded-counterexample-y k)
bounded-counterexample-eq k
  rewrite truncate-self (suc k)
        | truncate-suc-self k
  = refl

bounded-counterexample-breaks :
  ∀ k →
  boundedVec (suc k) (transportOrStay p2 (bounded-counterexample-x k))
    ≡
  boundedVec (suc k) (transportOrStay p2 (bounded-counterexample-y k))
    →
  ⊥
bounded-counterexample-breaks k eq
  rewrite truncate-step-self k
        | truncate-self (suc k)
  = nat-not-suc-self k (cong Vec15.e2 eq)

signedTransport-not-bounded :
  ∀ k →
  BoundedRespectsSignedTransport (suc k) → ⊥
signedTransport-not-bounded k respects =
  bounded-counterexample-breaks k
    (respects p2
      {x = bounded-counterexample-x k}
      {y = bounded-counterexample-y k}
      (bounded-counterexample-eq k))
