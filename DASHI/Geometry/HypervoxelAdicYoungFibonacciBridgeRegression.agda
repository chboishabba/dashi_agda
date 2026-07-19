module DASHI.Geometry.HypervoxelAdicYoungFibonacciBridgeRegression where

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Geometry.HypervoxelAdicYoungFibonacciBridge

all-bridges-remain-projections :
  ∀ {H A B G S}
  → (bridge : HypervoxelAdicYoungFibonacciBridge H A B G S)
  → HypervoxelAdicYoungFibonacciBridge.relation bridge ≡ projectedShadow
all-bridges-remain-projections = bridge-not-asserted-as-identity
