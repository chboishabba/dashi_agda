module DASHI.Geometry.LCP.TContractiveDepthGuarded where

open import Agda.Primitive using (Level)
open import Data.Nat using (ℕ)

open import DASHI.Geometry.LCP.Stream using (Stream; lcp≥)
open import DASHI.Geometry.LCP.ContractiveCompose using
  (Nonexpansive; Strictκ; Contractiveκ; Nonexp∘Strict∘Nonexp)
open import DASHI.Geometry.LCP.PStrictStatement using
  (P-strict-on-guard; Strictκ-from-guard)

module _ {ℓ} {A : Set ℓ} where

  postulate
    R : Stream A → Stream A
    P : Stream A → Stream A
    C : Stream A → Stream A

    R-nonexp : Nonexpansive R
    C-nonexp : Nonexpansive C

    κ : ℕ
    Guard : Stream A → Stream A → Set ℓ
    Guard-all : ∀ x y → Guard x y
    P-strict-guard : P-strict-on-guard κ P Guard

  T : Stream A → Stream A
  T x = C (P (R x))

  P-strict : Strictκ κ P
  P-strict = Strictκ-from-guard κ P Guard P-strict-guard Guard-all

  T-contract : Contractiveκ κ T
  T-contract =
    Nonexp∘Strict∘Nonexp κ C P R C-nonexp P-strict R-nonexp
