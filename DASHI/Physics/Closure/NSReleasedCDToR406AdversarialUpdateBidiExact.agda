module DASHI.Physics.Closure.NSReleasedCDToR406AdversarialUpdateBidiExact where

------------------------------------------------------------------------
-- RELEASED C/D -> R406 ADVERSARIAL UPDATE, WRONGTYPE-CORRECTED
--
-- Introspective correction.
--
-- The earlier R522/R525 vocabulary used the word `forcing` on both sides of
-- the comparison:
--
--   (1) the EXTERNAL body force f in the forced Navier--Stokes PDE used by
--       Clay alternatives C/D;
--
--   (2) the INTERNAL projected-nonlinearity / tangent / quadratic-companion
--       objects called forcing in the R406/R420/R423 unforced Galerkin lane.
--
-- Those are not the same formal or physical coordinate.
--
-- R423 is indexed by R240.PhysicalNSGalerkinTrajectory, whose equation owner is
-- the unforced projected Galerkin dynamics used by DASHI's A/B regularity lane.
-- The released C/D construction instead changes the PDE by adding a smooth
-- external body force.  Therefore the external f cannot be tested for
-- "membership in the R406 signed companion class" as though f itself were the
-- R406 companion.
--
-- Correct BIDI relation:
--
--   released external body force f
--     -> forced PDE trajectory / candidate
--     -> state-dependent internal nonlinear interactions on that trajectory
--     -> structural comparison with R406/R423 objects.
--
-- This may teach us which cancellation mechanisms survive under forcing, but
-- it is NOT a counterexample test for a theorem quantified only over the
-- unforced A/B trajectory class.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNClayExternalR406TriangleBidiRound525Exact as R525
import DASHI.Physics.Closure.NSTriadKNForcedBlowupR406BidiRound522Exact as R522
import DASHI.Physics.Closure.NSOpenAI2026ReleasedClayCDTorus369BidiExact as Release
import DASHI.Physics.Closure.NSOpenAI2026ComparatorClayCDSourceExactAlignment as Align
import DASHI.Physics.Closure.NSTriadKNQuadraticCompanionSignedHeatToBarrierRound423Exact as R423

------------------------------------------------------------------------
-- 1. Released source-to-Clay alignment really is closed.
------------------------------------------------------------------------

externalClayCStatementAlignmentClosed : Bool
externalClayCStatementAlignmentClosed = Align.releasedComparatorCExactlyMatchesClayC

externalClayDStatementAlignmentClosed : Bool
externalClayDStatementAlignmentClosed = Align.releasedComparatorDExactlyMatchesClayD

releasedPublicLeanPresent : Bool
releasedPublicLeanPresent = Release.roundOAI2026PublicLeanReleased

------------------------------------------------------------------------
-- 2. Distinguish the two meanings of forcing.
------------------------------------------------------------------------

data ForcingKind : Set where
  externalPDEBodyForce : ForcingKind
  internalStateDependentCompanion : ForcingKind

releasedForceKind : ForcingKind
releasedForceKind = externalPDEBodyForce

r406CompanionKind : ForcingKind
r406CompanionKind = internalStateDependentCompanion

data ExternalBodyForceEqualsInternalCompanionPermission : Set where

data ForcedTrajectoryAutomaticallyInhabitsUnforcedR240Permission : Set where

data ForcedCDCounterexampleAutomaticallyRefutesUnforcedABPermission : Set where

externalBodyForceDoesNotBecomeInternalCompanion :
  ExternalBodyForceEqualsInternalCompanionPermission → ⊥
externalBodyForceDoesNotBecomeInternalCompanion ()

forcedTrajectoryDoesNotAutomaticallyBecomeUnforcedR240 :
  ForcedTrajectoryAutomaticallyInhabitsUnforcedR240Permission → ⊥
forcedTrajectoryDoesNotAutomaticallyBecomeUnforcedR240 ()

forcedCDDoesNotAutomaticallyRefuteUnforcedAB :
  ForcedCDCounterexampleAutomaticallyRefutesUnforcedABPermission → ⊥
forcedCDDoesNotAutomaticallyRefuteUnforcedAB ()

------------------------------------------------------------------------
-- 3. Corrected residual order.
------------------------------------------------------------------------

data ReleasedR406Residual : Set where
  missingLiteralReleasedExternalForceIdentity : ReleasedR406Residual
  missingForcedTrajectorySemanticsInDASHI : ReleasedR406Residual
  missingInternalCompanionObservationOnForcedTrajectory : ReleasedR406Residual
  missingStructuralForcedVsUnforcedComparison : ReleasedR406Residual
  adversarialMechanismComparisonComplete : ReleasedR406Residual

data ReleasedR406Producer : Set where
  extractExactReleasedExternalForce : ReleasedR406Producer
  buildTypedForcedTrajectoryExtension : ReleasedR406Producer
  evaluateInternalNonlinearityOnForcedCandidate : ReleasedR406Producer
  compareCancellationMechanismsWithoutTypeCollapse : ReleasedR406Producer
  compileStructuralComparison : ReleasedR406Producer

producerFor : ReleasedR406Residual → ReleasedR406Producer
producerFor missingLiteralReleasedExternalForceIdentity =
  extractExactReleasedExternalForce
producerFor missingForcedTrajectorySemanticsInDASHI =
  buildTypedForcedTrajectoryExtension
producerFor missingInternalCompanionObservationOnForcedTrajectory =
  evaluateInternalNonlinearityOnForcedCandidate
producerFor missingStructuralForcedVsUnforcedComparison =
  compareCancellationMechanismsWithoutTypeCollapse
producerFor adversarialMechanismComparisonComplete = compileStructuralComparison

firstReleasedR406Residual : ReleasedR406Residual
firstReleasedR406Residual = missingLiteralReleasedExternalForceIdentity

------------------------------------------------------------------------
-- 4. Preserve historical R522/R525 facts without inheriting their type collapse.
------------------------------------------------------------------------

r525HistoricalClassInclusionQuestionRecorded :
  R525.round525FirstNewMissingCoordinateIsClassInclusion ≡ true
r525HistoricalClassInclusionQuestionRecorded =
  R525.round525FirstNewMissingCoordinateIsClassInclusionIsTrue

r522HistoricalBudgetMembershipQuestionRecorded :
  R522.round522MissingCoordinateIsSignedBudgetMembership ≡ true
r522HistoricalBudgetMembershipQuestionRecorded =
  R522.round522MissingCoordinateIsSignedBudgetMembershipIsTrue

-- The present owner supersedes that question as the canonical comparison:
-- before a membership test could even be meaningful, the two objects would
-- need to inhabit the same forcing type. R423 shows the live payment is instead
-- an internal quadratic-companion cross indexed by an unforced R240 trajectory.

round423CompanionFeedsUnforcedCriticalBarrier : Bool
round423CompanionFeedsUnforcedCriticalBarrier =
  R423.round423QuadraticCompanionSignedPaymentFeedsCriticalBarrier

------------------------------------------------------------------------
-- 5. Correct outcomes.
------------------------------------------------------------------------

data CorrectedAdversarialOutcome : Set where
  forcedConstructionInformsMechanismSearch : CorrectedAdversarialOutcome
  separatingEquationClassIdentified : CorrectedAdversarialOutcome

currentCorrectedOutcome : CorrectedAdversarialOutcome
currentCorrectedOutcome = separatingEquationClassIdentified

-- C/D and A/B differ first at the equation class: forced versus unforced.
-- Any deeper structural comparison is useful science, but not a logical
-- falsification of the unforced theorem.

------------------------------------------------------------------------
-- 6. Proof-search ledger.
------------------------------------------------------------------------

releasedSourceToClaySideClosed : Bool
releasedSourceToClaySideClosed = true

releasedExternalForceSameObjectAsR406Companion : Bool
releasedExternalForceSameObjectAsR406Companion = false

releasedForcedTrajectoryAlreadyInR240Class : Bool
releasedForcedTrajectoryAlreadyInR240Class = false

releasedCDDirectlyTestsUnforcedR406Theorem : Bool
releasedCDDirectlyTestsUnforcedR406Theorem = false

releasedForcedVsUnforcedStructuralComparisonClosed : Bool
releasedForcedVsUnforcedStructuralComparisonClosed = false

releasedSourceToClaySideClosedIsTrue : releasedSourceToClaySideClosed ≡ true
releasedSourceToClaySideClosedIsTrue = refl

releasedExternalForceSameObjectAsR406CompanionIsFalse :
  releasedExternalForceSameObjectAsR406Companion ≡ false
releasedExternalForceSameObjectAsR406CompanionIsFalse = refl

releasedForcedTrajectoryAlreadyInR240ClassIsFalse :
  releasedForcedTrajectoryAlreadyInR240Class ≡ false
releasedForcedTrajectoryAlreadyInR240ClassIsFalse = refl

releasedCDDirectlyTestsUnforcedR406TheoremIsFalse :
  releasedCDDirectlyTestsUnforcedR406Theorem ≡ false
releasedCDDirectlyTestsUnforcedR406TheoremIsFalse = refl
