module DASHI.Reasoning.AlbertF4LeanQFormAnisotropyValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.AlbertF4LeanQFormAnisotropyReceiptExact as Receipt

nativeQNormAnisotropySourceWritten :
  Receipt.Boundary.leanNativeQOctonionNormAnisotropySourceWritten Receipt.canonicalBoundary ≡ true
nativeQNormAnisotropySourceWritten = refl

nativeQNoZeroDivisorsSourceWritten :
  Receipt.Boundary.leanNativeQOctonionNoZeroDivisorsSourceWritten Receipt.canonicalBoundary ≡ true
nativeQNoZeroDivisorsSourceWritten = refl

qiChartIsScalarExtensionData :
  Receipt.Boundary.qiRootChartRecordedAsScalarExtensionData Receipt.canonicalBoundary ≡ true
qiChartIsScalarExtensionData = refl

qiChartDoesNotClassifyOriginalQForm :
  Receipt.Boundary.qiRootChartClassifiesOriginalQForm Receipt.canonicalBoundary ≡ false
qiChartDoesNotClassifyOriginalQForm = refl

leanAuthorityNotImported :
  Receipt.Boundary.leanKernelProofAuthorityImportedIntoAgda Receipt.canonicalBoundary ≡ false
leanAuthorityNotImported = refl

originalQClassificationOpen :
  Receipt.Boundary.originalQFormGroupClassificationPaid Receipt.canonicalBoundary ≡ false
originalQClassificationOpen = refl
