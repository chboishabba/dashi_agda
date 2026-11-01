module DASHI.Geometry.FiniteCausalDiamondMinimality where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Geometry.FiniteCausalDiamond as Diamond

------------------------------------------------------------------------
-- Exact observable receipts for the finite causal diamond.

separatorWidth : Diamond.SpatialSlice → Nat
separatorWidth Diamond.xyzSlice = 3

separatingSliceUnique :
  (slice : Diamond.SpatialSlice) →
  Diamond.Separates slice Diamond.past Diamond.future →
  slice ≡ Diamond.xyzSlice
separatingSliceUnique Diamond.xyzSlice
  Diamond.xyz-separates-past-future = refl

minimalSeparatingWidthIsThree :
  (slice : Diamond.SpatialSlice) →
  Diamond.Separates slice Diamond.past Diamond.future →
  separatorWidth slice ≡ 3
minimalSeparatingWidthIsThree Diamond.xyzSlice
  Diamond.xyz-separates-past-future = refl

chainLength : Diamond.Chain Diamond.past Diamond.future → Nat
chainLength Diamond.chain-via-x = 2
chainLength Diamond.chain-via-y = 2
chainLength Diamond.chain-via-z = 2

allPastFutureChainsHaveDepthTwo :
  (chain : Diamond.Chain Diamond.past Diamond.future) →
  chainLength chain ≡ 2
allPastFutureChainsHaveDepthTwo Diamond.chain-via-x = refl
allPastFutureChainsHaveDepthTwo Diamond.chain-via-y = refl
allPastFutureChainsHaveDepthTwo Diamond.chain-via-z = refl

record FiniteChainAntichainMinimalityReceipt : Set where
  constructor finite-chain-antichain-minimality
  field
    separatorUnique :
      (slice : Diamond.SpatialSlice) →
      Diamond.Separates slice Diamond.past Diamond.future →
      slice ≡ Diamond.xyzSlice
    separatorWidthThree :
      (slice : Diamond.SpatialSlice) →
      Diamond.Separates slice Diamond.past Diamond.future →
      separatorWidth slice ≡ 3
    chainDepthTwo :
      (chain : Diamond.Chain Diamond.past Diamond.future) →
      chainLength chain ≡ 2
open FiniteChainAntichainMinimalityReceipt public

canonicalFiniteChainAntichainMinimalityReceipt :
  FiniteChainAntichainMinimalityReceipt
canonicalFiniteChainAntichainMinimalityReceipt =
  finite-chain-antichain-minimality
    separatingSliceUnique
    minimalSeparatingWidthIsThree
    allPastFutureChainsHaveDepthTwo
