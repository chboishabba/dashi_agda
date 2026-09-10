module DASHI.Physics.Closure.NSReleasedCDToR406AdversarialUpdateBidiExact where

------------------------------------------------------------------------
-- RELEASED C/D -> EXISTING R525/R406 ADVERSARIAL UPDATE
--
-- R525 was written while the external smooth-forced NS construction was still
-- source-incomplete from DASHI's perspective.  The public OpenAI release now
-- pays the external->Clay theorem-identity side exactly at the comparator
-- surface.  Therefore the live adversarial question moves one step inward:
--
--   released exact Clay C/D witness
--     -> literal released forcing identity
--     -> instantiate on the SAME DASHI forcing carrier
--     -> decide membership in the exact signed critical forcing budget
--     -> if in class, use blowup as a falsification fixture for any theorem
--        quantified over that class;
--     -> if out of class, extract the precise separating hypothesis.
--
-- This owner does NOT assert that the released forcing is in or out of R406's
-- class.  That is the next mathematical same-object test.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNClayExternalR406TriangleBidiRound525Exact as R525
import DASHI.Physics.Closure.NSTriadKNForcedBlowupR406BidiRound522Exact as R522
import DASHI.Physics.Closure.NSOpenAI2026ReleasedClayCDTorus369BidiExact as Release
import DASHI.Physics.Closure.NSOpenAI2026ComparatorClayCDSourceExactAlignment as Align

------------------------------------------------------------------------
-- 1. What changed after release.
------------------------------------------------------------------------

externalClayCStatementAlignmentClosed : Bool
externalClayCStatementAlignmentClosed = Align.releasedClayCExactStatementAlignment

externalClayDStatementAlignmentClosed : Bool
externalClayDStatementAlignmentClosed = Align.releasedClayDExactStatementAlignment

releasedPublicLeanPresent : Bool
releasedPublicLeanPresent = Release.roundOAI2026PublicLeanReleased

------------------------------------------------------------------------
-- 2. Updated residual order.
------------------------------------------------------------------------

data ReleasedR406Residual : Set where
  missingLiteralReleasedForcingInstantiation : ReleasedR406Residual
  missingSignedBudgetMembershipDecision : ReleasedR406Residual
  missingR406QuantifierCompatibilityDecision : ReleasedR406Residual
  adversarialClassificationComplete : ReleasedR406Residual

data ReleasedR406Producer : Set where
  extractExactReleasedForcing : ReleasedR406Producer
  checkExactSignedBudgetMembership : ReleasedR406Producer
  auditLiteralR406QuantifierScope : ReleasedR406Producer
  compileInClassCounterexampleOrSeparator : ReleasedR406Producer

producerFor : ReleasedR406Residual → ReleasedR406Producer
producerFor missingLiteralReleasedForcingInstantiation = extractExactReleasedForcing
producerFor missingSignedBudgetMembershipDecision = checkExactSignedBudgetMembership
producerFor missingR406QuantifierCompatibilityDecision = auditLiteralR406QuantifierScope
producerFor adversarialClassificationComplete = compileInClassCounterexampleOrSeparator

firstReleasedR406Residual : ReleasedR406Residual
firstReleasedR406Residual = missingLiteralReleasedForcingInstantiation

------------------------------------------------------------------------
-- 3. BIDI outcomes once literal membership is known.
------------------------------------------------------------------------

data MembershipDecision : Set where
  releasedForcingInsideR406Class : MembershipDecision
  releasedForcingOutsideR406Class : MembershipDecision

data AdversarialOutcome : Set where
  candidateR406TheoremFacesConcreteCounterexample : AdversarialOutcome
  separatingHypothesisIdentified : AdversarialOutcome

outcomeFor : MembershipDecision → AdversarialOutcome
outcomeFor releasedForcingInsideR406Class =
  candidateR406TheoremFacesConcreteCounterexample
outcomeFor releasedForcingOutsideR406Class = separatingHypothesisIdentified

------------------------------------------------------------------------
-- 4. Preserve the old triangle, but retire its obsolete source uncertainty.
------------------------------------------------------------------------

r525OldFirstMissingCoordinateWasClassInclusion :
  R525.round525FirstNewMissingCoordinateIsClassInclusion ≡ true
r525OldFirstMissingCoordinateWasClassInclusion =
  R525.round525FirstNewMissingCoordinateIsClassInclusionIsTrue

r522MissingCoordinateStillBudgetMembership :
  R522.round522MissingCoordinateIsSignedBudgetMembership ≡ true
r522MissingCoordinateStillBudgetMembership =
  R522.round522MissingCoordinateIsSignedBudgetMembershipIsTrue

------------------------------------------------------------------------
-- 5. No shortcut: exact Clay alignment does not answer R406 membership.
------------------------------------------------------------------------

data ClayCDAdmissibilityImpliesR406BudgetMembershipPermission : Set where
data R406BudgetMembershipImpliesUnforcedABPaymentPermission : Set where

data ReleasedProofImpliesHistoricalDASHIPriorityPermission : Set where

clayCDDoesNotDetermineR406Membership :
  ClayCDAdmissibilityImpliesR406BudgetMembershipPermission → ⊥
clayCDDoesNotDetermineR406Membership ()

r406MembershipDoesNotPayUnforcedAB :
  R406BudgetMembershipImpliesUnforcedABPaymentPermission → ⊥
r406MembershipDoesNotPayUnforcedAB ()

releasedProofDoesNotRetroactivelyCreatePriority :
  ReleasedProofImpliesHistoricalDASHIPriorityPermission → ⊥
releasedProofDoesNotRetroactivelyCreatePriority ()

------------------------------------------------------------------------
-- 6. Proof-search ledger.
------------------------------------------------------------------------

releasedSourceToClaySideClosed : Bool
releasedSourceToClaySideClosed = true

releasedForcingLiteralSameObjectClosed : Bool
releasedForcingLiteralSameObjectClosed = false

releasedForcingR406MembershipClosed : Bool
releasedForcingR406MembershipClosed = false

releasedR406AdversarialClassificationClosed : Bool
releasedR406AdversarialClassificationClosed = false

releasedSourceToClaySideClosedIsTrue : releasedSourceToClaySideClosed ≡ true
releasedSourceToClaySideClosedIsTrue = refl

releasedForcingLiteralSameObjectClosedIsFalse :
  releasedForcingLiteralSameObjectClosed ≡ false
releasedForcingLiteralSameObjectClosedIsFalse = refl

releasedForcingR406MembershipClosedIsFalse :
  releasedForcingR406MembershipClosed ≡ false
releasedForcingR406MembershipClosedIsFalse = refl

releasedR406AdversarialClassificationClosedIsFalse :
  releasedR406AdversarialClassificationClosed ≡ false
releasedR406AdversarialClassificationClosedIsFalse = refl
