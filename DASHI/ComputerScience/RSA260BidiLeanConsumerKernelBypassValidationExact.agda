module DASHI.ComputerScience.RSA260BidiLeanConsumerKernelBypassValidationExact where

import DASHI.ComputerScience.RSA260BidiLeanConsumerKernelBypassExact as Owner

------------------------------------------------------------------------
-- RED/GREEN regression for the cross-prover generic consumer-kernel bypass.
------------------------------------------------------------------------

candidate : Owner.LeanConsumerKernelBypassCandidate
candidate = Owner.canonicalLeanConsumerKernelBypassCandidate

boundary : Owner.LeanConsumerKernelBypassBoundary
boundary = Owner.canonicalLeanConsumerKernelBypassBoundary

_ : Owner.leanSourceWritten candidate ≡ true
_ = refl

_ : Owner.leanKernelReceiptObserved candidate ≡ false
_ = refl

_ : Owner.crossProverTransportObserved candidate ≡ false
_ = refl

_ : Owner.rsaProductionBindingObserved candidate ≡ false
_ = refl

_ : Owner.genericJointKernelTheoremLocated boundary ≡ true
_ = refl

_ : Owner.genericJointKernelTheoremKernelCertified boundary ≡ false
_ = refl

_ : Owner.theoremCanReplaceRSASameObjectBinding boundary ≡ false
_ = refl
