module DASHI.Moonshine.OggSSP2BActualQ10RecognitionValidation where

------------------------------------------------------------------------
-- RED-FIRST validation for the post-Brauer actual-Q10 recognition contract.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.OggSSP2BActualQ10RecognitionContractExact as Target

validationCurrentActualQ10PaidIsFalse :
  Target.actualQ10SameObjectPaid Target.canonicalActualQ10AcquisitionBoundary ≡ false
validationCurrentActualQ10PaidIsFalse = refl

validationCurrentOuterDescentPaidIsFalse :
  Target.outerActionDescentPaid Target.canonicalActualQ10AcquisitionBoundary ≡ false
validationCurrentOuterDescentPaidIsFalse = refl

validationFiniteTenCandidatesPaidIsTrue :
  Target.finiteTenCandidatesPaid Target.canonicalActualQ10AcquisitionBoundary ≡ true
validationFiniteTenCandidatesPaidIsTrue = refl
