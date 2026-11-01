module DASHI.Geometry.BanachFixedPointNat where

open import Agda.Builtin.Equality using (_≡_)
open import Ultrametric as UMetric
open import Contraction as Contr
open import DASHI.Geometry.BanachFixedPoint as BFP

-- For ℕ-valued ultrametrics, a StrictContraction already packages the fixed point.
banachFromStrict :
  ∀ {S : Set} (U : UMetric.Ultrametric S) (T : S → S) →
  Contr.StrictContraction U T → BFP.BanachFixedPoint U T
banachFromStrict U T sc =
  record
    { fp = Contr.StrictContraction.fp sc
    ; fixes = Contr.StrictContraction.fixed sc
    ; unique = Contr.StrictContraction.unique sc
    }
