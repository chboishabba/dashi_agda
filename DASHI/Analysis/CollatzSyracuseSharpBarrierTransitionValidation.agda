module DASHI.Analysis.CollatzSyracuseSharpBarrierTransitionValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.CollatzSyracuseSharpBarrierTransitionExact as Barrier

lateEvenMonotonePaid :
  Barrier.SharpBarrierTransitionBoundary.trailingEvenSharpThresholdNonincreasingPaid
    Barrier.canonicalSharpBarrierTransitionBoundary
  ≡ 1
lateEvenMonotonePaid = refl

familyCompressionPaid :
  Barrier.SharpBarrierTransitionBoundary.arbitraryTrailingEvenSharpThresholdNonincreasingPaid
    Barrier.canonicalSharpBarrierTransitionBoundary
  ≡ 1
familyCompressionPaid = refl

oddMonotonicityNotClaimed :
  Barrier.SharpBarrierTransitionBoundary.trailingOddSharpThresholdAlwaysNonincreasing
    Barrier.canonicalSharpBarrierTransitionBoundary
  ≡ 0
oddMonotonicityNotClaimed = refl
