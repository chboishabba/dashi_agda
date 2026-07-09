module DASHI.Physics.ClaySupportingBKMIntegralBridge where

open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties
  using ( ≤-refl; ≤-trans; *-monoʳ-≤ )

----------------------------------------------------------------------
-- §1  BKM integral bridge: projection sum to vorticity integral
----------------------------------------------------------------------

record BKMIntegralBridge : Set where
  field
    vorticitySupIntegral : Nat
    finiteProjectionSum : Nat
    projectionConstant  : Nat
    bridgeBound : vorticitySupIntegral ≤ projectionConstant * finiteProjectionSum

----------------------------------------------------------------------
-- §2  Composability: finiteProjectionSum ≤ B ⇒ vorticitySupIntegral ≤ C_proj * B
----------------------------------------------------------------------

applyFiniteProjectionSumBound :
  (bridge : BKMIntegralBridge) → (B : Nat) →
  BKMIntegralBridge.finiteProjectionSum bridge ≤ B →
  BKMIntegralBridge.vorticitySupIntegral bridge
    ≤
  BKMIntegralBridge.projectionConstant bridge * B
applyFiniteProjectionSumBound bridge B sumBound =
  ≤-trans (BKMIntegralBridge.bridgeBound bridge)
          (*-monoʳ-≤ (BKMIntegralBridge.projectionConstant bridge) sumBound)

----------------------------------------------------------------------
-- §3  Canonical zero bridge (fail‑closed default)
----------------------------------------------------------------------

trivialBKMIntegralBridge : BKMIntegralBridge
trivialBKMIntegralBridge = record
  { vorticitySupIntegral  = 0
  ; finiteProjectionSum  = 0
  ; projectionConstant   = 0
  ; bridgeBound          = ≤-refl {0}
  }
