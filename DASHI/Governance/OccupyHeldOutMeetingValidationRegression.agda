module DASHI.Governance.OccupyHeldOutMeetingValidationRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.OccupyHeldOutMeetingValidationExact as HeldOut

alreadyInspectedCannotBeRetrofitted :
  HeldOut.alreadyInspectedMeetingCountsAsProspectiveHeldOut
    HeldOut.canonicalHeldOutBoundary
  ≡ false
alreadyInspectedCannotBeRetrofitted = refl

corpusMaterialisationPaid :
  HeldOut.corpusMaterialisationPaid HeldOut.canonicalHeldOutBoundary ≡ true
corpusMaterialisationPaid = refl

manifestFreezePaid :
  HeldOut.corpusManifestFreezePaid HeldOut.canonicalHeldOutBoundary ≡ true
manifestFreezePaid = refl

holdoutAssignmentPaid :
  HeldOut.holdoutAssignmentPaid HeldOut.canonicalHeldOutBoundary ≡ true
holdoutAssignmentPaid = refl

outcomeBlindSelectionRequired :
  HeldOut.selectionRuleMustBeOutcomeBlindAndDeterministic
    HeldOut.canonicalHeldOutBoundary
  ≡ true
outcomeBlindSelectionRequired = refl

codingRuleFreezeRequired :
  HeldOut.codingProtocolMustBeFrozenBeforeHeldOutOutcomeExtraction
    HeldOut.canonicalHeldOutBoundary
  ≡ true
codingRuleFreezeRequired = refl

heldOutOutcomeExtractionStillUnpaid :
  HeldOut.heldOutOutcomeExtractionPaid HeldOut.canonicalHeldOutBoundary ≡ false
heldOutOutcomeExtractionStillUnpaid = refl

heldOutEvaluationStillUnpaid :
  HeldOut.heldOutEvaluationPaid HeldOut.canonicalHeldOutBoundary ≡ false
heldOutEvaluationStillUnpaid = refl

prospectiveValidationStillUnpaid :
  HeldOut.prospectiveHeldOutValidationPaid HeldOut.canonicalHeldOutBoundary ≡ false
prospectiveValidationStillUnpaid = refl
