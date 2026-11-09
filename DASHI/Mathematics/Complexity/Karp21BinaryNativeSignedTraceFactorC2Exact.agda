module DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedTraceFactorC2Exact where

------------------------------------------------------------------------
-- Original SSP sign inversion as a concrete operation on N21 Karp
-- signed binary trace classes. No Monster quotient is claimed.
--
-- The C2 action swaps positive and negative lanes and keeps the
-- original binary magnitude and occurrence-count bytes unchanged.
-- The actual bit-native factor replay commutes with the involution.
--
-- Imported original SSP polarity bridge is not transitively --safe;
-- this source owner likewise makes no safe/kernel-acceptance claim.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.List.Base using (List)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.Complexity.Karp21SignedSSPOrientationNoLosslessExact as SSP
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedTraceFactorExact as Factor

flipClass : Factor.SignedWeightClass → Factor.SignedWeightClass
flipClass (weight , count) = SSP.flipBinarySign weight , count

flipClasses :
  Factor.SignedTraceFactors → Factor.SignedTraceFactors
flipClasses [] = []
flipClasses (factor ∷ rest) = flipClass factor ∷ flipClasses rest

swapLedger : Ledger.SignedLedger → Ledger.SignedLedger
swapLedger (positive , negative) = negative , positive

swapLedgerInvolutive :
  (ledger : Ledger.SignedLedger) →
  swapLedger (swapLedger ledger) ≡ ledger
swapLedgerInvolutive (positive , negative) = refl

flipClassInvolutive :
  (factor : Factor.SignedWeightClass) →
  flipClass (flipClass factor) ≡ factor
flipClassInvolutive (Signed.positive bits , count) = refl
flipClassInvolutive (Signed.negative bits , count) = refl

flipClassesInvolutive :
  (factors : Factor.SignedTraceFactors) →
  flipClasses (flipClasses factors) ≡ factors
flipClassesInvolutive [] = refl
flipClassesInvolutive (factor ∷ rest) =
  trans
    (cong (λ x → x ∷ flipClasses (flipClasses rest))
      (flipClassInvolutive factor))
    (cong (factor ∷_) (flipClassesInvolutive rest))

sameWeightSignFlipInvariant :
  (x y : Signed.SignedMagnitudeBits) →
  Factor.sameSignedToken (SSP.flipBinarySign x) (SSP.flipBinarySign y)
    ≡ Factor.sameSignedToken x y
sameWeightSignFlipInvariant (Signed.positive x) (Signed.positive y) = refl
sameWeightSignFlipInvariant (Signed.positive x) (Signed.negative y) = refl
sameWeightSignFlipInvariant (Signed.negative x) (Signed.positive y) = refl
sameWeightSignFlipInvariant (Signed.negative x) (Signed.negative y) = refl

insertFactorCommutesWithSignFlip :
  (factor : Factor.SignedWeightClass) (ledger : Ledger.SignedLedger) →
  swapLedger (Factor.insertFactor factor ledger) ≡
    Factor.insertFactor (flipClass factor) (swapLedger ledger)
insertFactorCommutesWithSignFlip (Signed.positive bits , count)
  (positive , negative) = refl
insertFactorCommutesWithSignFlip (Signed.negative bits , count)
  (positive , negative) = refl

-- The core concrete C2 equivariance: same factored binary arithmetic
-- kernel, interchanging ONLY which sign lane receives each result.
factorReplayCommutesWithSignFlip :
  (factors : Factor.SignedTraceFactors) (ledger : Ledger.SignedLedger) →
  swapLedger (Factor.replayFactors factors ledger) ≡
    Factor.replayFactors (flipClasses factors) (swapLedger ledger)
factorReplayCommutesWithSignFlip [] ledger = refl
factorReplayCommutesWithSignFlip (factor ∷ rest) ledger =
  trans
    (factorReplayCommutesWithSignFlip rest
      (Factor.insertFactor factor ledger))
    (cong (Factor.replayFactors (flipClasses rest))
      (insertFactorCommutesWithSignFlip factor ledger))

-- The original (unfactored) executable ledger has the very same C2
-- sign symmetry; hence the factor replay does not invent a new one.
insertSignedCommutesWithSignFlip :
  (weight : Signed.SignedMagnitudeBits) (ledger : Ledger.SignedLedger) →
  swapLedger (Ledger.insertSigned weight ledger) ≡
    Ledger.insertSigned (SSP.flipBinarySign weight)
      (swapLedger ledger)
insertSignedCommutesWithSignFlip (Signed.positive magnitude)
  (positive , negative) = refl
insertSignedCommutesWithSignFlip (Signed.negative magnitude)
  (positive , negative) = refl
