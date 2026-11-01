module DASHI.Physics.CliffordBridge where

-- Clifford-like adapter boundary: spinor/algebra slots only, no semantics.

open import DASHI.Physics.Bridge using (BridgeSurface)

record CliffordAdapter : Set₁ where
  field
    bridge : BridgeSurface

open CliffordAdapter public
