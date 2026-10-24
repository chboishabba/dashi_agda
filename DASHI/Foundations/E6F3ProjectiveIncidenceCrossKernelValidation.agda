module DASHI.Foundations.E6F3ProjectiveIncidenceCrossKernelValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.E6F3ProjectiveIncidenceCrossKernelReceiptExact as Receipt

lagCount40 : Receipt.projectiveLagrangianCount Receipt.canonicalReceipt ≡ 40
lagCount40 = refl

nullCount40 : Receipt.projectiveStandardNullCount Receipt.canonicalReceipt ≡ 40
nullCount40 = refl

degree12 : Receipt.projectiveDegree Receipt.canonicalReceipt ≡ 12
degree12 = refl

adjacentCommon2 : Receipt.projectiveAdjacentCommon Receipt.canonicalReceipt ≡ 2
adjacentCommon2 = refl

nonAdjacentCommon4 : Receipt.projectiveNonAdjacentCommon Receipt.canonicalReceipt ≡ 4
nonAdjacentCommon4 = refl

sameObjectSourceWritten :
  Receipt.projectiveLagStandardNullEquivalenceLeanSourceWritten Receipt.canonicalBoundary ≡ true
sameObjectSourceWritten = refl

incidenceOrthogonalitySourceWritten :
  Receipt.incidenceOrthogonalityEquivalenceLeanSourceWritten Receipt.canonicalBoundary ≡ true
incidenceOrthogonalitySourceWritten = refl

srg401224SourceWritten :
  Receipt.projectiveSRG401224LeanSourceWritten Receipt.canonicalBoundary ≡ true
srg401224SourceWritten = refl

rawT4StillDistinct :
  Receipt.rawPuncturedT4PromotedToLagCarrier Receipt.canonicalBoundary ≡ false
rawT4StillDistinct = refl

end DASHI.Foundations.E6F3ProjectiveIncidenceCrossKernelValidation
