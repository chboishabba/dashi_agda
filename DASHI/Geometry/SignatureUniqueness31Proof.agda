module DASHI.Geometry.SignatureUniqueness31Proof where

open import Level using (Level; suc)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Geometry.EnergyAdditivityProof

data Signature : Set where
  sig31 : Signature
  sig13 : Signature
  other : Signature

record QuadraticFormSpace {ℓ}
  (A : Additive {ℓ}) (F : ScalarField {ℓ}) : Set (suc ℓ) where
  open Additive A
  open ScalarField F
  field
    Q : Carrier → Scalar

open QuadraticFormSpace public

record ConeStructure {ℓ} (X : Set ℓ) : Set (suc ℓ) where
  field Cone : X → Set ℓ

record Arrow {ℓ} (X : Set ℓ) : Set (suc ℓ) where
  field _≺_ : X → X → Set ℓ

record Isotropy {ℓ} (X : Set ℓ) : Set (suc ℓ) where
  field
    G   : Set ℓ
    _•_ : G → X → X

record SignatureAxioms {ℓ}
  {A : Additive {ℓ}} {F : ScalarField {ℓ}}
  (V : QuadraticFormSpace A F) : Set (suc ℓ) where
  open Additive A
  open ScalarField F
  field
    ConeS : ConeStructure Carrier
    Arr   : Arrow Carrier
    Iso   : Isotropy Carrier

    Timelike : Carrier → Set ℓ
    cone→time : ∀ x → ConeStructure.Cone ConeS x → Timelike x
    time→cone : ∀ x → Timelike x → ConeStructure.Cone ConeS x

    presCone  : ∀ g x → ConeStructure.Cone ConeS x → ConeStructure.Cone ConeS (Isotropy._•_ Iso g x)
    presQ     : ∀ g x → Q V (Isotropy._•_ Iso g x) ≡ Q V x

    arrow-orients : ∀ x → Timelike x → ⊤

    atMostOneNegativeDirection : ⊤
    spatialIsotropyForces3 : ⊤

SignatureUniqueness31 :
  ∀ {ℓ} {A : Additive {ℓ}} {F : ScalarField {ℓ}}
  (V : QuadraticFormSpace A F) →
  SignatureAxioms V →
  Signature
SignatureUniqueness31 V ax = sig31
