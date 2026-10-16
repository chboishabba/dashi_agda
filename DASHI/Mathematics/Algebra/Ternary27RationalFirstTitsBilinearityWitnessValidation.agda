module DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsBilinearityWitnessValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsBilinearityWitnessExact as Bilinear

bilinearitySourceWritten :
  Bilinear.fullFirstTitsBilinearityTermSourceWritten Bilinear.canonicalBoundary ≡ true
bilinearitySourceWritten = refl

classificationNotUsed :
  Bilinear.externalAlbertClassificationUsed Bilinear.canonicalBoundary ≡ false
classificationNotUsed = refl

kernelReceiptStillSeparate :
  Bilinear.exactHeadAgdaKernelReceiptPresent Bilinear.canonicalBoundary ≡ false
kernelReceiptStillSeparate = refl
