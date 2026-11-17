{-# OPTIONS --safe #-}
module DASHI.Interop.FP16SupportBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Requested capability and reported support are not device validation.
data FP16Decision : Set where
  denied : FP16Decision
  permittedByReceipt : FP16Decision

record FP16SupportRequest : Set where
  constructor fp16SupportRequest
  field
    requested : Bool
    reportedSupported : Bool

decideFP16 : FP16SupportRequest → FP16Decision
decideFP16 (fp16SupportRequest true true) = permittedByReceipt
decideFP16 (fp16SupportRequest true false) = denied
decideFP16 (fp16SupportRequest false true) = denied
decideFP16 (fp16SupportRequest false false) = denied

unsupportedDenied : decideFP16 (fp16SupportRequest true false) ≡ denied
unsupportedDenied = refl

notRequestedDenied : (supported : Bool) →
  decideFP16 (fp16SupportRequest false supported) ≡ denied
notRequestedDenied true = refl
notRequestedDenied false = refl

receiptAllowsOnlyRequested : decideFP16 (fp16SupportRequest true true) ≡ permittedByReceipt
receiptAllowsOnlyRequested = refl
