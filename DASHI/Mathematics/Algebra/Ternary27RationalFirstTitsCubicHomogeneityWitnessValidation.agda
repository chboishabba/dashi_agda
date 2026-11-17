module DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsCubicHomogeneityWitnessValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsCubicHomogeneityWitnessExact as Cubic

cubicHomogeneitySourceWritten :
  Cubic.cubicHomogeneityTermSourceWritten Cubic.canonicalBoundary ≡ true
cubicHomogeneitySourceWritten = refl

classificationNotUsed :
  Cubic.externalAlbertClassificationUsed Cubic.canonicalBoundary ≡ false
classificationNotUsed = refl

kernelReceiptStillSeparate :
  Cubic.exactHeadAgdaKernelReceiptPresent Cubic.canonicalBoundary ≡ false
kernelReceiptStillSeparate = refl
