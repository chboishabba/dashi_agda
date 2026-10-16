module DASHI.Physics.CondensedMatter.MATBGQTMResolutionKernelValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.CondensedMatter.MATBGQTMResolutionKernelReceiptExact as R

resolution-coordinates-source-paid : R.sourceResolutionCoordinatesPaid R.canonicalQTMResolutionKernelBoundary ≡ true
resolution-coordinates-source-paid = refl

synthetic-kernel-executed : R.normalizedSyntheticKernelExecuted R.canonicalQTMResolutionKernelBoundary ≡ true
synthetic-kernel-executed = refl

gaussian-model-is-not-measured-response : R.gaussianResponseSourceMeasured R.canonicalQTMResolutionKernelReceipt ≡ false
gaussian-model-is-not-measured-response = refl

resolution-kernel-is-not-qtm-fit : R.interactingQTMFitPaid R.canonicalQTMResolutionKernelReceipt ≡ false
resolution-kernel-is-not-qtm-fit = refl
