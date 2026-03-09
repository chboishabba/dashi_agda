module DASHI.Geometry.RealIsotropy.Core where

open import Ultrametric as UMetric
open import DASHI.Geometry.Isotropy as Iso

record RealIsotropy {S : Set} (U : UMetric.Ultrametric S) (T : S → S) : Set₁ where
  field
    iso : Iso.Isotropy U T
    coneInvariant : Set
