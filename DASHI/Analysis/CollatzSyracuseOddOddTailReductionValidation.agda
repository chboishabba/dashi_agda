module DASHI.Analysis.CollatzSyracuseOddOddTailReductionValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.CollatzSyracuseOddOddTailReductionExact as Reduction

oddEvenCylinderPaid :
  Reduction.OddOddTailReductionBoundary.oddEvenTwoStepDescentPaid
    Reduction.canonicalOddOddTailReductionBoundary
  ≡ 1
oddEvenCylinderPaid = refl

oddOddCompilerPaid :
  Reduction.OddOddTailReductionBoundary.oddOddTailCompilerPaid
    Reduction.canonicalOddOddTailReductionBoundary
  ≡ 1
oddOddCompilerPaid = refl

oddOddProducerStillOpen :
  Reduction.OddOddTailReductionBoundary.oddOddTailProducerPaid
    Reduction.canonicalOddOddTailReductionBoundary
  ≡ 0
oddOddProducerStillOpen = refl
