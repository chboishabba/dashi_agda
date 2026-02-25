module DASHI.Energy.EnergySplitProof where

open import Level using (Level; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Energy.ClosestPoint
open import DASHI.Geometry.QuadraticEmergence
open import DASHI.Core.Q using (_+ℚ_)

record EnergySplit
  {ℓ}
  {X : Set ℓ}
  (QS : QuadraticStructure X)
  (Pj : Projection X)
  : Set (suc ℓ) where
  field
    split :
      ∀ x →
        QuadraticStructure.Q QS x
        ≡
        (QuadraticStructure.Q QS (Projection.P Pj x))
        +ℚ
        (QuadraticStructure.Q QS
          (QuadraticStructure._-_ QS x (Projection.P Pj x)))
