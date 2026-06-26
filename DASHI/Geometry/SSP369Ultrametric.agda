module DASHI.Geometry.SSP369Ultrametric where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; _⊓_; _⊔_; _∸_; z≤n; s≤s)
open import Data.Nat.Properties as NatP
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import Ultrametric as UMetric

_≢_ : {A : Set} → A → A → Set
_≢_ {A} x y = x ≡ y → ⊥

data Digit369 : Set where
  digit3 : Digit369
  digit6 : Digit369
  digit9 : Digit369

Address : Nat → Set
Address d = Vec Digit369 d

addressDepth : ∀ {d : Nat} → Address d → Nat
addressDepth {d} _ = d

data PrefixMatch : ∀ {d : Nat} → Nat → Address d → Address d → Set where
  prefix-zero :
    ∀ {d : Nat} {x y : Address d} →
    PrefixMatch zero x y

  prefix-cons :
    ∀ {d k : Nat} (a : Digit369) {xs ys : Address d} →
    PrefixMatch k xs ys →
    PrefixMatch (suc k) (a ∷ xs) (a ∷ ys)

agreementDepth : ∀ {d : Nat} → Address d → Address d → Nat
agreementDepth [] [] = zero
agreementDepth (digit3 ∷ xs) (digit3 ∷ ys) = suc (agreementDepth xs ys)
agreementDepth (digit6 ∷ xs) (digit6 ∷ ys) = suc (agreementDepth xs ys)
agreementDepth (digit9 ∷ xs) (digit9 ∷ ys) = suc (agreementDepth xs ys)
agreementDepth _ _ = zero

distance : ∀ {d : Nat} → Address d → Address d → Nat
distance {d} x y = d ∸ agreementDepth x y

prefixWitness : ∀ {d : Nat} (x y : Address d) → PrefixMatch (agreementDepth x y) x y
prefixWitness [] [] = prefix-zero
prefixWitness (x ∷ xs) (y ∷ ys) with x | y
... | digit3 | digit3 = prefix-cons digit3 (prefixWitness xs ys)
... | digit6 | digit6 = prefix-cons digit6 (prefixWitness xs ys)
... | digit9 | digit9 = prefix-cons digit9 (prefixWitness xs ys)
... | digit3 | digit6 = prefix-zero
... | digit3 | digit9 = prefix-zero
... | digit6 | digit3 = prefix-zero
... | digit6 | digit9 = prefix-zero
... | digit9 | digit3 = prefix-zero
... | digit9 | digit6 = prefix-zero

prefixMatch-sound : ∀ {d k : Nat} {x y : Address d} → PrefixMatch k x y → k ≤ agreementDepth x y
prefixMatch-sound prefix-zero = z≤n
prefixMatch-sound (prefix-cons digit3 p) = s≤s (prefixMatch-sound p)
prefixMatch-sound (prefix-cons digit6 p) = s≤s (prefixMatch-sound p)
prefixMatch-sound (prefix-cons digit9 p) = s≤s (prefixMatch-sound p)

prefixMatch→distanceBound :
  ∀ {d k : Nat} {x y : Address d} →
  PrefixMatch k x y →
  distance {d} x y ≤ d ∸ k
prefixMatch→distanceBound {d} p =
  NatP.∸-monoʳ-≤ d (prefixMatch-sound p)

agreementDepth-self : ∀ {d : Nat} (x : Address d) → agreementDepth x x ≡ d
agreementDepth-self [] = refl
agreementDepth-self (digit3 ∷ xs) = cong suc (agreementDepth-self xs)
agreementDepth-self (digit6 ∷ xs) = cong suc (agreementDepth-self xs)
agreementDepth-self (digit9 ∷ xs) = cong suc (agreementDepth-self xs)

prefixMatch-refl : ∀ {d : Nat} (x : Address d) → PrefixMatch d x x
prefixMatch-refl {d} x = subst (λ k → PrefixMatch k x x) (agreementDepth-self x) (prefixWitness x x)

agreementDepth-symmetric : ∀ {d : Nat} (x y : Address d) → agreementDepth x y ≡ agreementDepth y x
agreementDepth-symmetric [] [] = refl
agreementDepth-symmetric (x ∷ xs) (y ∷ ys) with x | y
... | digit3 | digit3 = cong suc (agreementDepth-symmetric xs ys)
... | digit6 | digit6 = cong suc (agreementDepth-symmetric xs ys)
... | digit9 | digit9 = cong suc (agreementDepth-symmetric xs ys)
... | digit3 | digit6 = refl
... | digit3 | digit9 = refl
... | digit6 | digit3 = refl
... | digit6 | digit9 = refl
... | digit9 | digit3 = refl
... | digit9 | digit6 = refl

agreementDepth≤depth : ∀ {d : Nat} (x y : Address d) → agreementDepth x y ≤ d
agreementDepth≤depth [] [] = z≤n
agreementDepth≤depth (x ∷ xs) (y ∷ ys) with x | y
... | digit3 | digit3 = s≤s (agreementDepth≤depth xs ys)
... | digit6 | digit6 = s≤s (agreementDepth≤depth xs ys)
... | digit9 | digit9 = s≤s (agreementDepth≤depth xs ys)
... | digit3 | digit6 = z≤n
... | digit3 | digit9 = z≤n
... | digit6 | digit3 = z≤n
... | digit6 | digit9 = z≤n
... | digit9 | digit3 = z≤n
... | digit9 | digit6 = z≤n

agreementDepth-full→equal :
  ∀ {d : Nat} (x y : Address d) →
  agreementDepth x y ≡ d →
  x ≡ y
agreementDepth-full→equal [] [] _ = refl
agreementDepth-full→equal (digit3 ∷ xs) (digit3 ∷ ys) eq =
  cong (digit3 ∷_) (agreementDepth-full→equal xs ys (NatP.suc-injective eq))
agreementDepth-full→equal (digit6 ∷ xs) (digit6 ∷ ys) eq =
  cong (digit6 ∷_) (agreementDepth-full→equal xs ys (NatP.suc-injective eq))
agreementDepth-full→equal (digit9 ∷ xs) (digit9 ∷ ys) eq =
  cong (digit9 ∷_) (agreementDepth-full→equal xs ys (NatP.suc-injective eq))
agreementDepth-full→equal (digit3 ∷ xs) (digit6 ∷ ys) ()
agreementDepth-full→equal (digit3 ∷ xs) (digit9 ∷ ys) ()
agreementDepth-full→equal (digit6 ∷ xs) (digit3 ∷ ys) ()
agreementDepth-full→equal (digit6 ∷ xs) (digit9 ∷ ys) ()
agreementDepth-full→equal (digit9 ∷ xs) (digit3 ∷ ys) ()
agreementDepth-full→equal (digit9 ∷ xs) (digit6 ∷ ys) ()

distance-self-zero : ∀ {d : Nat} (x : Address d) → distance x x ≡ zero
distance-self-zero {d} x =
  trans
    (cong (λ k → d ∸ k) (agreementDepth-self x))
    (NatP.n∸n≡0 d)

distance-symmetric : ∀ {d : Nat} (x y : Address d) → distance x y ≡ distance y x
distance-symmetric {d} x y =
  cong (λ k → d ∸ k) (agreementDepth-symmetric x y)

distance-zero→equal :
  ∀ {d : Nat} (x y : Address d) →
  distance x y ≡ zero →
  x ≡ y
distance-zero→equal {d} x y d0 =
  let
    full≤ : d ≤ agreementDepth x y
    full≤ = NatP.m∸n≡0⇒m≤n d0

    agree≤ : agreementDepth x y ≤ d
    agree≤ = agreementDepth≤depth x y

    agree≡full : agreementDepth x y ≡ d
    agree≡full = NatP.≤-antisym agree≤ full≤
  in
  agreementDepth-full→equal x y agree≡full

distance-nonzero :
  ∀ {d : Nat} {x y : Address d} →
  x ≢ y →
  distance x y ≢ zero
distance-nonzero x≢y d0 = x≢y (distance-zero→equal _ _ d0)

agreementDepth-triangle :
  ∀ {d : Nat} (x y z : Address d) →
  (agreementDepth x y ⊓ agreementDepth y z) ≤ agreementDepth x z
agreementDepth-triangle [] [] [] = z≤n
agreementDepth-triangle (x ∷ xs) (y ∷ ys) (z ∷ zs) with x | y | z
... | digit3 | digit3 | digit3 = s≤s (agreementDepth-triangle xs ys zs)
... | digit6 | digit6 | digit6 = s≤s (agreementDepth-triangle xs ys zs)
... | digit9 | digit9 | digit9 = s≤s (agreementDepth-triangle xs ys zs)
... | digit3 | digit3 | digit6 = z≤n
... | digit3 | digit3 | digit9 = z≤n
... | digit3 | digit6 | digit3 = z≤n
... | digit3 | digit6 | digit6 = z≤n
... | digit3 | digit6 | digit9 = z≤n
... | digit3 | digit9 | digit3 = z≤n
... | digit3 | digit9 | digit6 = z≤n
... | digit3 | digit9 | digit9 = z≤n
... | digit6 | digit3 | digit3 = z≤n
... | digit6 | digit3 | digit6 = z≤n
... | digit6 | digit3 | digit9 = z≤n
... | digit6 | digit6 | digit3 = z≤n
... | digit6 | digit6 | digit9 = z≤n
... | digit6 | digit9 | digit3 = z≤n
... | digit6 | digit9 | digit6 = z≤n
... | digit6 | digit9 | digit9 = z≤n
... | digit9 | digit3 | digit3 = z≤n
... | digit9 | digit3 | digit6 = z≤n
... | digit9 | digit3 | digit9 = z≤n
... | digit9 | digit6 | digit3 = z≤n
... | digit9 | digit6 | digit6 = z≤n
... | digit9 | digit6 | digit9 = z≤n
... | digit9 | digit9 | digit3 = z≤n
... | digit9 | digit9 | digit6 = z≤n

ultrametric369 : ∀ {d : Nat} → UMetric.Ultrametric (Address d)
ultrametric369 {d} =
  record
    { d = distance {d}
    ; id-zero = distance-self-zero
    ; symmetric = distance-symmetric
    ; ultratriangle = ultra
    }
  where
    ultra : ∀ x y z → distance {d} x z ≤ (distance {d} x y ⊔ distance {d} y z)
    ultra x y z =
      let
        a = agreementDepth x y
        b = agreementDepth y z
        c = agreementDepth x z
        step1 : d ∸ c ≤ d ∸ (a ⊓ b)
        step1 = NatP.∸-monoʳ-≤ d (agreementDepth-triangle x y z)

        step2 : d ∸ (a ⊓ b) ≡ (d ∸ a) ⊔ (d ∸ b)
        step2 = NatP.∸-distribˡ-⊓-⊔ d a b
      in
      NatP.≤-trans step1 (NatP.≤-reflexive step2)
