module DASHI.Geometry.LCP.InductiveLimit where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; _≤_; z≤n; _⊔_)
open import Data.Product using (Σ; _,_; _×_)

open import DASHI.Geometry.LCP.NatGlue using (≤-⊔-l; ≤-⊔-r)

------------------------------------------------------------------------
-- Directed Nat-indexed colimit machinery.
--
-- The repo already uses Nat-indexed depth towers and concrete filtered
-- colimit surfaces.  This module packages the reusable Nat-directed
-- interface once, together with a concrete constant-diagram colimit
-- instance that can serve as a safe base case for inductive-limit
-- constructions.

natDirectedness :
  ∀ (m n : ℕ) →
  Σ ℕ (λ k → m ≤ k × n ≤ k)
natDirectedness m n =
  m ⊔ n ,
  (≤-⊔-l m n , ≤-⊔-r m n)

record NatDiagram : Setω where
  field
    Obj :
      ℕ →
      Set

    map :
      ∀ {m n} →
      m ≤ n →
      Obj m →
      Obj n

open NatDiagram public

record NatCocone (D : NatDiagram) (X : Set) : Setω where
  field
    leg :
      (n : ℕ) →
      Obj D n →
      X

    commute :
      ∀ {m n} →
      (m≤n : m ≤ n) →
      (x : Obj D m) →
      leg m x
      ≡
      leg n (map D m≤n x)

open NatCocone public

record NatColimitWitness (D : NatDiagram) : Setω where
  field
    Colimit :
      Set

    ι :
      (n : ℕ) →
      Obj D n →
      Colimit

    mediator :
      {X : Set} →
      NatCocone D X →
      Colimit →
      X

    mediator-factor :
      {X : Set} →
      (c : NatCocone D X) →
      (n : ℕ) →
      (x : Obj D n) →
      mediator c (ι n x)
      ≡
      leg c n x

    mediator-unique :
      {X : Set} →
      (c : NatCocone D X) →
      (f : Colimit → X) →
      (∀ (n : ℕ) (x : Obj D n) → f (ι n x) ≡ leg c n x) →
      ∀ y → f y ≡ mediator c y

    colimitBoundary :
      List String

open NatColimitWitness public

constantNatDiagram :
  Set →
  NatDiagram
constantNatDiagram A =
  record
    { Obj = λ _ → A
    ; map = λ _ x → x
    }

constantNatCocone :
  ∀ {A X : Set} →
  (f : A → X) →
  NatCocone (constantNatDiagram A) X
constantNatCocone f =
  record
    { leg = λ _ → f
    ; commute = λ _ _ → refl
    }

constantNatColimitWitness :
  ∀ (A : Set) →
  NatColimitWitness (constantNatDiagram A)
constantNatColimitWitness A =
  record
    { Colimit = A
    ; ι = λ _ x → x
    ; mediator = λ c → leg c 0
    ; mediator-factor = λ c n x → commute c z≤n x
    ; mediator-unique = λ c f factor y → factor 0 y
    ; colimitBoundary =
        "Nat-directed colimit machinery packages a reusable Nat-indexed cocone interface"
        ∷ "The constant diagram is the concrete inhabited colimit base case"
        ∷ "The mediator is the 0-leg and the factorization law is pointwise"
        ∷ []
    }

constantNatColimitBoundary :
  List String
constantNatColimitBoundary =
  "Constant Nat colimit witness is concrete, inhabited, and cycle-free"
  ∷ "It can be reused as the stable base case for future inductive-limit towers"
  ∷ []

