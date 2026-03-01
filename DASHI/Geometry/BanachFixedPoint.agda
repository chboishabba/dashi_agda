module DASHI.Geometry.BanachFixedPoint where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Ultrametric as UMetric
open import Contraction as Contr
open import DASHI.Geometry.CompleteUltrametric as CU

record BanachFixedPoint {S : Set}
  (U : UMetric.Ultrametric S)
  (T : S → S) : Set₁ where
  field
    fp     : S
    fixes  : T fp ≡ fp
    unique : ∀ x → T x ≡ x → x ≡ fp

-- Interface theorem: completeness + contraction ⇒ fixed point (no proof yet).
postulate
  banach :
    ∀ {S : Set} (U : UMetric.Ultrametric S) (T : S → S) →
    CU.Complete U → Contr.Contractive U T → BanachFixedPoint U T

open BanachFixedPoint public
