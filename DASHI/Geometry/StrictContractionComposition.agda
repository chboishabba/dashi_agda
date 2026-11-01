module DASHI.Geometry.StrictContractionComposition where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_; _<_)
open import Ultrametric as UMetric
open import Contraction as Contraction using (_≢_; Contractive≢)

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

infixr 9 _∘_
record NonExpansive {S : Set} (U : UMetric.Ultrametric S) (f : S → S) : Set₁ where
  open UMetric.Ultrametric U
  field
    nonexp : ∀ x y → d (f x) (f y) ≤ d x y

record DistinctPreserving {S : Set} (g : S → S) : Set₁ where
  field
    preserves≢ : ∀ {x y} → x ≢ y → g x ≢ g y

record OrderLaws : Set₁ where
  field
    le-trans   : ∀ {a b c : Nat} → a ≤ b → b ≤ c → a ≤ c
    le-<-trans : ∀ {a b c : Nat} → a ≤ b → b < c → a < c
    <-le-trans : ∀ {a b c : Nat} → a < b → b ≤ c → a < c

-- If f and g are nonexpansive and h is strictly contractive, then f ∘ h ∘ g is strictly contractive.
composeStrict :
  ∀ {S : Set} (U : UMetric.Ultrametric S)
    (f g h : S → S) →
  OrderLaws →
  NonExpansive U f →
  NonExpansive U g →
  DistinctPreserving g →
  Contraction.Contractive≢ U h →
  Contraction.Contractive≢ U (f ∘ (h ∘ g))
composeStrict U f g h laws neF neG dpG sh =
  record
    { contraction≢ = λ {x} {y} x≢y →
        let open UMetric.Ultrametric U
            open Contraction.Contractive≢ sh
            open OrderLaws laws
            step1 = NonExpansive.nonexp neF (h (g x)) (h (g y))
            step2 = contraction≢ {x = g x} {y = g y} (DistinctPreserving.preserves≢ dpG x≢y)
            step3 = NonExpansive.nonexp neG x y
        in
        <-le-trans (le-<-trans step1 step2) step3
    }
