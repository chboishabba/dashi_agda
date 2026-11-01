module DASHI.Geometry.EnergySplitProof where

open import Level using (Level; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)
open import Data.Unit using (⊤; tt)

open import DASHI.Geometry.EnergyAdditivityProof

record ProjectionDefect {ℓ} (A : Additive {ℓ}) : Set (suc ℓ) where
  open Additive A
  field
    P      : Additive.Carrier A → Additive.Carrier A
    D      : Additive.Carrier A → Additive.Carrier A
    D-def  : ∀ x → D x ≡ Additive._+_ A x (Additive.-_ A (P x))
    P-idem : ∀ x → P (P x) ≡ P x
    decomp : ∀ x → x ≡ Additive._+_ A (P x) (D x)

open ProjectionDefect public

EnergySplitProof :
  ∀ {ℓ} {A : Additive {ℓ}} {F : ScalarField {ℓ}}
  (V : InnerProductSpace A F) (T2 : Two F)
  (PD : ProjectionDefect A) →
  (∀ x → Orth V (P PD x) (D PD x)) →
  -- NOTE: this is the local lemma form. The canonical closure pipeline routes
  -- projection-defect energy splitting through
  -- `DASHI.Geometry.ProjectionDefectToParallelogram` / `DASHI.Geometry.QuadraticFormEmergence`.
  (∀ x y → Orth V x y → E V ( _+_ A x y ) ≡ ( _+s_ F (E V x) (E V y) )) →
  ∀ x → E V x ≡ ( _+s_ F (E V (P PD x)) (E V (D PD x)) )
EnergySplitProof {A = A} {F = F} V _ PD orthPD addE x =
  let open Additive A
      open ScalarField F
      open InnerProductSpace V
      open ProjectionDefect PD
  in
  trans (cong (InnerProductSpace.E V) (ProjectionDefect.decomp PD x))
        (addE (ProjectionDefect.P PD x) (ProjectionDefect.D PD x) (orthPD x))
