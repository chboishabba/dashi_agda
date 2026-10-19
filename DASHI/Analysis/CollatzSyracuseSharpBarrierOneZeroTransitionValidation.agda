module DASHI.Analysis.CollatzSyracuseSharpBarrierOneZeroTransitionValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.CollatzSyracuseSharpBarrierOneZeroTransitionExact as Pair

pairContracts :
  Pair.SharpBarrierOneZeroBoundary.trailingOneZeroAlwaysContractsPaid
    Pair.canonicalSharpBarrierOneZeroBoundary
  ≡ 1
pairContracts = refl

pairBarrierMonotone :
  Pair.SharpBarrierOneZeroBoundary.trailingOneZeroSharpThresholdNonincreasingPaid
    Pair.canonicalSharpBarrierOneZeroBoundary
  ≡ 1
pairBarrierMonotone = refl

noUniversalPromotion :
  Pair.SharpBarrierOneZeroBoundary.localOneZeroLawCreatesUniversalEscape
    Pair.canonicalSharpBarrierOneZeroBoundary
  ≡ 0
noUniversalPromotion = refl
