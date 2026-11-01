module DASHI.Geometry.LCP.TContractiveDepth where

open import Agda.Primitive using (Level)
open import Data.Nat using (ℕ)

open import DASHI.Geometry.LCP.Stream using (Stream)
open import DASHI.Geometry.LCP.ContractiveCompose using
  (Nonexpansive; Strictκ; Contractiveκ; Nonexp∘Strict∘Nonexp)

module _ {ℓ} {A : Set ℓ}
         (R P C : Stream A → Stream A)
         (R-nonexp : Nonexpansive R)
         (C-nonexp : Nonexpansive C)
         (κ : ℕ)
         (P-strict : Strictκ κ P)
         where

  T : Stream A → Stream A
  T x = C (P (R x))

  T-contract : Contractiveκ κ T
  T-contract =
    Nonexp∘Strict∘Nonexp κ C P R C-nonexp P-strict R-nonexp
