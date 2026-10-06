module DASHI.Governance.OccupyHeldOutMeetingValidationRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.OccupyHeldOutMeetingValidationExact as HeldOut

alreadyInspectedCannotBeRetrofitted :
  HeldOut.alreadyInspectedMeetingCountsAsProspectiveHeldOut
    HeldOut.canonicalHeldOutBoundary
  ≡ false
alreadyInspectedCannotBeRetrofitted = refl

freezeBeforeCodingRequired :
  HeldOut.heldOutSetMustBeFrozenBeforeOutcomeCoding
    HeldOut.canonicalHeldOutBoundary
  ≡ true
freezeBeforeCodingRequired = refl

codingRuleFreezeRequired :
  HeldOut.codingProtocolMustBeFrozenBeforeHeldOutExtraction
    HeldOut.canonicalHeldOutBoundary
  ≡ true
codingRuleFreezeRequired = refl

manifestFreezeRequired :
  HeldOut.corpusManifestMustBeFrozenBeforeSelection
    HeldOut.canonicalHeldOutBoundary
  ≡ true
manifestFreezeRequired = refl

deterministicSelectionRequired :
  HeldOut.selectionRuleMustBeOutcomeBlindAndDeterministic
    HeldOut.canonicalHeldOutBoundary
  ≡ true
deterministicSelectionRequired = refl

currentArchiveHasNoProspectiveHeldOutReceipt :
  HeldOut.prospectiveHeldOutValidationPaid
    HeldOut.canonicalHeldOutBoundary
  ≡ false
currentArchiveHasNoProspectiveHeldOutReceipt = refl
