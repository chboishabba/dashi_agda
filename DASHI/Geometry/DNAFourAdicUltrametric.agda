module DASHI.Geometry.DNAFourAdicUltrametric where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; _⊓_; _⊔_; _∸_; z≤n; s≤s)
open import Data.Nat.Properties as NatP
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import Ultrametric as UMetric
import DASHI.Biology.DNAChemistryCarrier as DNA

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

Address : Nat → Set
Address d = Vec DNA.DNABase d

agreementDepth : ∀ {d : Nat} → Address d → Address d → Nat
agreementDepth [] [] = zero
agreementDepth (DNA.A ∷ xs) (DNA.A ∷ ys) = suc (agreementDepth xs ys)
agreementDepth (DNA.C ∷ xs) (DNA.C ∷ ys) = suc (agreementDepth xs ys)
agreementDepth (DNA.G ∷ xs) (DNA.G ∷ ys) = suc (agreementDepth xs ys)
agreementDepth (DNA.T ∷ xs) (DNA.T ∷ ys) = suc (agreementDepth xs ys)
agreementDepth _ _ = zero

distance : ∀ {d : Nat} → Address d → Address d → Nat
distance {d} x y = d ∸ agreementDepth x y

agreementDepth-self : ∀ {d : Nat} (x : Address d) → agreementDepth x x ≡ d
agreementDepth-self [] = refl
agreementDepth-self (DNA.A ∷ xs) = cong suc (agreementDepth-self xs)
agreementDepth-self (DNA.C ∷ xs) = cong suc (agreementDepth-self xs)
agreementDepth-self (DNA.G ∷ xs) = cong suc (agreementDepth-self xs)
agreementDepth-self (DNA.T ∷ xs) = cong suc (agreementDepth-self xs)

agreementDepth-symmetric : ∀ {d : Nat} (x y : Address d) → agreementDepth x y ≡ agreementDepth y x
agreementDepth-symmetric [] [] = refl
agreementDepth-symmetric (x ∷ xs) (y ∷ ys) with x | y
... | DNA.A | DNA.A = cong suc (agreementDepth-symmetric xs ys)
... | DNA.C | DNA.C = cong suc (agreementDepth-symmetric xs ys)
... | DNA.G | DNA.G = cong suc (agreementDepth-symmetric xs ys)
... | DNA.T | DNA.T = cong suc (agreementDepth-symmetric xs ys)
... | DNA.A | DNA.C = refl
... | DNA.A | DNA.G = refl
... | DNA.A | DNA.T = refl
... | DNA.C | DNA.A = refl
... | DNA.C | DNA.G = refl
... | DNA.C | DNA.T = refl
... | DNA.G | DNA.A = refl
... | DNA.G | DNA.C = refl
... | DNA.G | DNA.T = refl
... | DNA.T | DNA.A = refl
... | DNA.T | DNA.C = refl
... | DNA.T | DNA.G = refl

agreementDepth≤depth : ∀ {d : Nat} (x y : Address d) → agreementDepth x y ≤ d
agreementDepth≤depth [] [] = z≤n
agreementDepth≤depth (x ∷ xs) (y ∷ ys) with x | y
... | DNA.A | DNA.A = s≤s (agreementDepth≤depth xs ys)
... | DNA.C | DNA.C = s≤s (agreementDepth≤depth xs ys)
... | DNA.G | DNA.G = s≤s (agreementDepth≤depth xs ys)
... | DNA.T | DNA.T = s≤s (agreementDepth≤depth xs ys)
... | DNA.A | DNA.C = z≤n
... | DNA.A | DNA.G = z≤n
... | DNA.A | DNA.T = z≤n
... | DNA.C | DNA.A = z≤n
... | DNA.C | DNA.G = z≤n
... | DNA.C | DNA.T = z≤n
... | DNA.G | DNA.A = z≤n
... | DNA.G | DNA.C = z≤n
... | DNA.G | DNA.T = z≤n
... | DNA.T | DNA.A = z≤n
... | DNA.T | DNA.C = z≤n
... | DNA.T | DNA.G = z≤n

agreementDepth-full→equal :
  ∀ {d : Nat} (x y : Address d) →
  agreementDepth x y ≡ d →
  x ≡ y
agreementDepth-full→equal [] [] _ = refl
agreementDepth-full→equal (DNA.A ∷ xs) (DNA.A ∷ ys) eq =
  cong (DNA.A ∷_) (agreementDepth-full→equal xs ys (NatP.suc-injective eq))
agreementDepth-full→equal (DNA.C ∷ xs) (DNA.C ∷ ys) eq =
  cong (DNA.C ∷_) (agreementDepth-full→equal xs ys (NatP.suc-injective eq))
agreementDepth-full→equal (DNA.G ∷ xs) (DNA.G ∷ ys) eq =
  cong (DNA.G ∷_) (agreementDepth-full→equal xs ys (NatP.suc-injective eq))
agreementDepth-full→equal (DNA.T ∷ xs) (DNA.T ∷ ys) eq =
  cong (DNA.T ∷_) (agreementDepth-full→equal xs ys (NatP.suc-injective eq))
agreementDepth-full→equal (DNA.A ∷ xs) (DNA.C ∷ ys) ()
agreementDepth-full→equal (DNA.A ∷ xs) (DNA.G ∷ ys) ()
agreementDepth-full→equal (DNA.A ∷ xs) (DNA.T ∷ ys) ()
agreementDepth-full→equal (DNA.C ∷ xs) (DNA.A ∷ ys) ()
agreementDepth-full→equal (DNA.C ∷ xs) (DNA.G ∷ ys) ()
agreementDepth-full→equal (DNA.C ∷ xs) (DNA.T ∷ ys) ()
agreementDepth-full→equal (DNA.G ∷ xs) (DNA.A ∷ ys) ()
agreementDepth-full→equal (DNA.G ∷ xs) (DNA.C ∷ ys) ()
agreementDepth-full→equal (DNA.G ∷ xs) (DNA.T ∷ ys) ()
agreementDepth-full→equal (DNA.T ∷ xs) (DNA.A ∷ ys) ()
agreementDepth-full→equal (DNA.T ∷ xs) (DNA.C ∷ ys) ()
agreementDepth-full→equal (DNA.T ∷ xs) (DNA.G ∷ ys) ()

distance-self-zero : ∀ {d : Nat} (x : Address d) → distance x x ≡ zero
distance-self-zero {d} x =
  trans (cong (λ k → d ∸ k) (agreementDepth-self x)) (NatP.n∸n≡0 d)

distance-symmetric : ∀ {d : Nat} (x y : Address d) → distance x y ≡ distance y x
distance-symmetric {d} x y =
  cong (λ k → d ∸ k) (agreementDepth-symmetric x y)

distance-zero→equal :
  ∀ {d : Nat} (x y : Address d) →
  distance x y ≡ zero →
  x ≡ y
distance-zero→equal {d} x y d0 =
  agreementDepth-full→equal x y
    (NatP.≤-antisym
      (agreementDepth≤depth x y)
      (NatP.m∸n≡0⇒m≤n d0))

agreementDepth-triangle :
  ∀ {d : Nat} (x y z : Address d) →
  (agreementDepth x y ⊓ agreementDepth y z) ≤ agreementDepth x z
agreementDepth-triangle [] [] [] = z≤n
agreementDepth-triangle (x ∷ xs) (y ∷ ys) (z ∷ zs) with x | y | z
... | DNA.A | DNA.A | DNA.A = s≤s (agreementDepth-triangle xs ys zs)
... | DNA.C | DNA.C | DNA.C = s≤s (agreementDepth-triangle xs ys zs)
... | DNA.G | DNA.G | DNA.G = s≤s (agreementDepth-triangle xs ys zs)
... | DNA.T | DNA.T | DNA.T = s≤s (agreementDepth-triangle xs ys zs)
... | DNA.A | DNA.A | DNA.C = z≤n
... | DNA.A | DNA.A | DNA.G = z≤n
... | DNA.A | DNA.A | DNA.T = z≤n
... | DNA.A | DNA.C | DNA.A = z≤n
... | DNA.A | DNA.C | DNA.C = z≤n
... | DNA.A | DNA.C | DNA.G = z≤n
... | DNA.A | DNA.C | DNA.T = z≤n
... | DNA.A | DNA.G | DNA.A = z≤n
... | DNA.A | DNA.G | DNA.C = z≤n
... | DNA.A | DNA.G | DNA.G = z≤n
... | DNA.A | DNA.G | DNA.T = z≤n
... | DNA.A | DNA.T | DNA.A = z≤n
... | DNA.A | DNA.T | DNA.C = z≤n
... | DNA.A | DNA.T | DNA.G = z≤n
... | DNA.A | DNA.T | DNA.T = z≤n
... | DNA.C | DNA.A | DNA.A = z≤n
... | DNA.C | DNA.A | DNA.C = z≤n
... | DNA.C | DNA.A | DNA.G = z≤n
... | DNA.C | DNA.A | DNA.T = z≤n
... | DNA.C | DNA.C | DNA.A = z≤n
... | DNA.C | DNA.C | DNA.G = z≤n
... | DNA.C | DNA.C | DNA.T = z≤n
... | DNA.C | DNA.G | DNA.A = z≤n
... | DNA.C | DNA.G | DNA.C = z≤n
... | DNA.C | DNA.G | DNA.G = z≤n
... | DNA.C | DNA.G | DNA.T = z≤n
... | DNA.C | DNA.T | DNA.A = z≤n
... | DNA.C | DNA.T | DNA.C = z≤n
... | DNA.C | DNA.T | DNA.G = z≤n
... | DNA.C | DNA.T | DNA.T = z≤n
... | DNA.G | DNA.A | DNA.A = z≤n
... | DNA.G | DNA.A | DNA.C = z≤n
... | DNA.G | DNA.A | DNA.G = z≤n
... | DNA.G | DNA.A | DNA.T = z≤n
... | DNA.G | DNA.C | DNA.A = z≤n
... | DNA.G | DNA.C | DNA.C = z≤n
... | DNA.G | DNA.C | DNA.G = z≤n
... | DNA.G | DNA.C | DNA.T = z≤n
... | DNA.G | DNA.G | DNA.A = z≤n
... | DNA.G | DNA.G | DNA.C = z≤n
... | DNA.G | DNA.G | DNA.T = z≤n
... | DNA.G | DNA.T | DNA.A = z≤n
... | DNA.G | DNA.T | DNA.C = z≤n
... | DNA.G | DNA.T | DNA.G = z≤n
... | DNA.G | DNA.T | DNA.T = z≤n
... | DNA.T | DNA.A | DNA.A = z≤n
... | DNA.T | DNA.A | DNA.C = z≤n
... | DNA.T | DNA.A | DNA.G = z≤n
... | DNA.T | DNA.A | DNA.T = z≤n
... | DNA.T | DNA.C | DNA.A = z≤n
... | DNA.T | DNA.C | DNA.C = z≤n
... | DNA.T | DNA.C | DNA.G = z≤n
... | DNA.T | DNA.C | DNA.T = z≤n
... | DNA.T | DNA.G | DNA.A = z≤n
... | DNA.T | DNA.G | DNA.C = z≤n
... | DNA.T | DNA.G | DNA.G = z≤n
... | DNA.T | DNA.G | DNA.T = z≤n
... | DNA.T | DNA.T | DNA.A = z≤n
... | DNA.T | DNA.T | DNA.C = z≤n
... | DNA.T | DNA.T | DNA.G = z≤n

ultrametricDNA : ∀ {d : Nat} → UMetric.Ultrametric (Address d)
ultrametricDNA {d} =
  record
    { d = distance {d}
    ; id-zero = distance-self-zero
    ; symmetric = distance-symmetric
    ; ultratriangle = ultra
    }
  where
  ultra : ∀ x y z → distance {d} x z ≤ (distance {d} x y ⊔ distance {d} y z)
  ultra x y z =
    NatP.≤-trans
      (NatP.∸-monoʳ-≤ d (agreementDepth-triangle x y z))
      (NatP.≤-reflexive (NatP.∸-distribˡ-⊓-⊔ d (agreementDepth x y) (agreementDepth y z)))
