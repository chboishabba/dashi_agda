module DASHI.Reasoning.AlbertF4LeanNormStabilizerSameObjectValidation where

import DASHI.Reasoning.AlbertF4LeanNormStabilizerSameObjectReceiptExact as R

open R

_ : canonicalReceipt.sameLiteralRationalAlbertCarrier ≡ true
_ = refl

_ : canonicalReceipt.normUnitMembershipIffJordanMembershipSourceWrittenInLean ≡ true
_ = refl

_ : canonicalReceipt.externalSourceTheoremAttributedToDASHI ≡ false
_ = refl

_ : canonicalReceipt.crossKernelProofAuthorityTransferred ≡ false
_ = refl
