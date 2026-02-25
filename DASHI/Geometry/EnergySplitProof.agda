module DASHI.Geometry.EnergySplitProof where

open import Level using (Level; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)
open import Data.Unit using (⊤; tt)

open import DASHI.Geometry.EnergyAdditivityProof

record ProjectionDefect {ℓ} (A : Additive {ℓ}) : Set (suc ℓ) where
  open Additive A
  field
    P      : Carrier → Carrier
    D      : Carrier → Carrier
    D-def  : ∀ x → D x ≡ x + (- (P x))
    P-idem : ∀ x → P (P x) ≡ P x
    decomp : ∀ x → x ≡ (P x) + (D x)

open ProjectionDefect public

EnergySplitProof :
  ∀ {ℓ} {A : Additive {ℓ}} {F : ScalarField {ℓ}}
  (V : InnerProductSpace A F) (T2 : Two F)
  (PD : ProjectionDefect A) →
  (∀ x → Orth V (P PD x) (D PD x)) →
  (∀ x y → Orth V x y → E V ( _+_ A x y ) ≡ ( _+s_ F (E V x) (E V y) )) →
  ∀ x → E V x ≡ ( _+s_ F (E V (P PD x)) (E V (D PD x)) )
EnergySplitProof {A = A} {F = F} V T2 PD orthPD addE x =
  let open Additive A
      open ScalarField F
      open InnerProductSpace V
      open ProjectionDefect PD
  in
  trans (cong (E V) (decomp x))
        (addE (P x) (D x) (orthPD x))
