module DASHI.Foundations.E6F3ProjectiveIncidenceCrossKernelValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.E6F3ProjectiveIncidenceCrossKernelReceiptExact as Receipt

lagCount40 : Receipt.projectiveLagrangianCount Receipt.canonicalReceipt ≡ 40
lagCount40 = refl

nullCount40 : Receipt.projectiveStandardNullCount Receipt.canonicalReceipt ≡ 40
nullCount40 = refl

sameObjectSourceWritten :
  Receipt.projectiveLagStandardNullEquivalenceLeanSourceWritten Receipt.canonicalBoundary ≡ true
sameObjectSourceWritten = refl

incidenceOrthogonalitySourceWritten :
  Receipt.incidenceOrthogonalityEquivalenceLeanSourceWritten Receipt.canonicalBoundary ≡ true
incidenceOrthogonalitySourceWritten = refl

rawT4StillDistinct :
  Receipt.rawPuncturedT4PromotedToLagCarrier Receipt.canonicalBoundary ≡ false
rawT4StillDistinct = refl

end DASHI.Foundations.E6F3ProjectiveIncidenceCrossKernelValidation
