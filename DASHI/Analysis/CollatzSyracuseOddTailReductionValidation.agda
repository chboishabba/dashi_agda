module DASHI.Analysis.CollatzSyracuseOddTailReductionValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.CollatzSyracuseOddTailReductionExact as Reduction

oddTailCompilerOwned :
  Reduction.OddTailReductionBoundary.oddTailCompilerPaid
    Reduction.canonicalOddTailReductionBoundary
  ≡ 1
oddTailCompilerOwned = refl

evenStartsPaid :
  Reduction.OddTailReductionBoundary.evenStartsStrictDescentPaid
    Reduction.canonicalOddTailReductionBoundary
  ≡ 1
evenStartsPaid = refl

oddTailStillOpen :
  Reduction.OddTailReductionBoundary.oddTailProducerPaid
    Reduction.canonicalOddTailReductionBoundary
  ≡ 0
oddTailStillOpen = refl
