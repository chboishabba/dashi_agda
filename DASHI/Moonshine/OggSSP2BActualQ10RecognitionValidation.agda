module DASHI.Moonshine.OggSSP2BActualQ10RecognitionValidation where

------------------------------------------------------------------------
-- RED-FIRST validation for the post-Brauer actual-Q10 recognition contract
-- and the terminal two-producer factorisation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.OggSSP2BActualQ10RecognitionContractExact as Target
import DASHI.Moonshine.OggSSP2BTerminalRecognitionProductExact as Terminal

validationCurrentActualQ10PaidIsFalse :
  Target.actualQ10SameObjectPaid Target.canonicalActualQ10AcquisitionBoundary ≡ false
validationCurrentActualQ10PaidIsFalse = refl

validationCurrentOuterDescentPaidIsFalse :
  Target.outerActionDescentPaid Target.canonicalActualQ10AcquisitionBoundary ≡ false
validationCurrentOuterDescentPaidIsFalse = refl

validationFiniteTenCandidatesPaidIsTrue :
  Target.finiteTenCandidatesPaid Target.canonicalActualQ10AcquisitionBoundary ≡ true
validationFiniteTenCandidatesPaidIsTrue = refl

validationTerminalCoreStillOpen :
  Terminal.sameObjectQ10AndOuterDescentPaid Terminal.canonicalTerminal2BMaxCut ≡ false
validationTerminalCoreStillOpen = refl

validationTerminalDefectSourceStillOpen :
  Terminal.independentTwoBitDefectSourcePaid Terminal.canonicalTerminal2BMaxCut ≡ false
validationTerminalDefectSourceStillOpen = refl

validation31NotRequired :
  Terminal.downstream31PromotionRequired Terminal.canonicalTerminal2BMaxCut ≡ false
validation31NotRequired = refl

validation279NotRequired :
  Terminal.downstream279PromotionRequired Terminal.canonicalTerminal2BMaxCut ≡ false
validation279NotRequired = refl
