module DASHI.MDL.MDLDescentProof where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import DASHI.Energy.Core
open import DASHI.Energy.ClosestPoint

record MDL {ℓx ℓe} (X : Set ℓx) (E : Set ℓe) : Set (lsuc (ℓx ⊔ ℓe)) where
  field
    mdl : X → E

record AddOps {ℓ} (X : Set ℓ) : Set (lsuc ℓ) where
  field
    _+_ : X → X → X
    _-_ : X → X → X

record AddOpsE {ℓ} (E : Set ℓ) : Set (lsuc ℓ) where
  field
    _+E_ : E → E → E

record MDLSplit
  {ℓx ℓe}
  {X : Set ℓx} {E : Set ℓe}
  (Pr : Projection X)
  (Ops : AddOps X)
  (OpsE : AddOpsE E)
  (M : MDL X E)
  : Set (lsuc (ℓx ⊔ ℓe)) where
  open AddOps Ops
  open AddOpsE OpsE
  field
    model : X → E
    resid : X → E
    split : ∀ x → MDL.mdl M x ≡ model (Projection.P Pr x) +E resid (x - Projection.P Pr x)

record Descent
  {ℓx ℓe}
  {X : Set ℓx} {E : Set ℓe}
  (ES : EnergySpace X E)
  (T : X → X)
  (M : MDL X E)
  : Set (lsuc (ℓx ⊔ ℓe)) where
  field
    descent : ∀ x →
      Preorder._≤_ (EnergySpace.P ES)
        (MDL.mdl M (T x))
        (MDL.mdl M x)
