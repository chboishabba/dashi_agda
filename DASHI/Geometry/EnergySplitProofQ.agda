module DASHI.Geometry.EnergySplitProofQ where

open import Agda.Primitive using (lzero)
open import DASHI.Geometry.EnergyAdditivityProof
open import DASHI.Geometry.EnergyAdditivityProofQ
open import DASHI.Geometry.EnergySplitProof

-- Convenience wrapper: apply EnergySplitProof with ℚ scalar laws.
EnergySplitProofℚ :
  ∀ {A : Additive {lzero}}
  (V : InnerProductSpace A scalarFieldℚ) (T2 : Two scalarFieldℚ)
  (PD : ProjectionDefect A) →
  (∀ x → Orth V (P PD x) (D PD x)) →
  ∀ x → E V x ≡ (_+s_ scalarFieldℚ (E V (P PD x)) (E V (D PD x)))
EnergySplitProofℚ V T2 PD orthPD =
  let addE = EnergyAdditivityProofℚ V T2 (λ x y o → o)
  in
  EnergySplitProof V T2 PD orthPD addE
