module DASHI.Reasoning.AlbertF4LeanDescentClassificationValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.AlbertF4LeanDescentClassificationReceiptExact as Receipt

adapterTyped : Receipt.sameObjectDescentAdapterTyped Receipt.canonicalBoundary ≡ true
adapterTyped = refl

adapterNotInhabited : Receipt.sameObjectDescentAdapterInhabited Receipt.canonicalBoundary ≡ false
adapterNotInhabited = refl

crossKernelAuthorityNotTransferred :
  Receipt.crossKernelProofAuthorityTransferred Receipt.canonicalBoundary ≡ false
crossKernelAuthorityNotTransferred = refl
