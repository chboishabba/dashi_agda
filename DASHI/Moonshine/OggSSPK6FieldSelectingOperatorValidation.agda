module DASHI.Moonshine.OggSSPK6FieldSelectingOperatorValidation where

------------------------------------------------------------------------
-- Validation surface for the post-no-go K6 field selector.
--
-- The original RED state required one independently sourced F3-linear
-- endomorphism of the existing X6 carrier, a literal swap01-breaking witness,
-- and a degree-six/cyclic generator receipt.  Cross-pollination with the
-- Monster-3B ATLAS compression lane now pays that acquisition/executable seam.
-- Full action/orbit/stabilizer recognition and Agda-kernel replay of the literal
-- 6x6 intertwiner remain deliberately separate.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSPK6FieldSelectingOperatorExact as Target

validationRequiredMinimalPolynomialDegree :
  Target.minimalPolynomialDegree Target.canonicalAcquisitionTarget ≡ 6
validationRequiredMinimalPolynomialDegree = refl

validationRequiredCyclicSpanDimension :
  Target.cyclicSpanDimension Target.canonicalAcquisitionTarget ≡ 6
validationRequiredCyclicSpanDimension = refl

validationIndependentSourceNowLocated :
  Target.independentlyOwnedOperatorLocated Target.canonicalAcquisitionTarget ≡ true
validationIndependentSourceNowLocated = refl

validationSameCarrierWeldNowPaid :
  Target.actualSameCarrierIntertwinerPaid Target.canonicalAcquisitionTarget ≡ true
validationSameCarrierWeldNowPaid = refl

validationFullActionRecognitionStillOpen :
  Target.actionOrbitStabilizerRecognitionPaid Target.canonicalAcquisitionTarget ≡ false
validationFullActionRecognitionStillOpen = refl

validationLeanLiteralIntertwinerSourceWritten :
  Target.companionLeanLiteralMatrixIntertwinerSourceWritten
    Target.canonicalCurrentBoundary ≡ true
validationLeanLiteralIntertwinerSourceWritten = refl

validationAgdaKernelReplayStillOpen :
  Target.agdaLiteralMatrixIntertwinerKernelPaid Target.canonicalCurrentBoundary ≡ false
validationAgdaKernelReplayStillOpen = refl
