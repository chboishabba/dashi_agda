module DASHI.Culture.AmyEskridgePostDeathTransitionSnowballWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Culture.MissingDeceasedOverlookedDimensionMatrixExact as Matrix
import DASHI.Culture.AmyEskridgeApplicationTransformationExact as App
import DASHI.Culture.AmyEskridgeCorporateCustodySurfaceExact as Custody
import DASHI.Culture.AmyEskridgeCorporateInstitutionalChronologySnowballExact as Chron

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: POST-DEATH TRANSITION SNOWBALL WELD
--
-- This is a thin adapter over existing owners.  The general missing/deceased
-- matrix already names Amy's 2020-2022 Institute/HoloChron apparatus,
-- repository, notebook, governance and custody frontier.  The application
-- transformation owner already asks for successor/handover; the custody owner
-- already asks for post-death asset disposition and officer transitions.  The
-- newer institutional chronology supplies retained OSINT observations only.
------------------------------------------------------------------------

matrixAmyEventTimeStillPartial :
  Matrix.eventTimeAlignment Matrix.eskridgeRow ≡ Matrix.partial
matrixAmyEventTimeStillPartial = refl

matrixAmyOrganisationStillPartial :
  Matrix.organisationalTransition Matrix.eskridgeRow ≡ Matrix.partial
matrixAmyOrganisationStillPartial = refl

matrixAmyCustodyStillOpen :
  Matrix.physicalOrDataCustody Matrix.eskridgeRow ≡ Matrix.open
matrixAmyCustodyStillOpen = refl

applicationSuccessorStillUnrecovered :
  App.successorOrHandoverRecovered App.canonicalAmyApplicationTransformationFrontier ≡ false
applicationSuccessorStillUnrecovered = refl

holochronDissolutionRemainsSecondaryLead :
  Chron.entitlement Chron.holochronDissolutionLeadAtom ≡ Chron.secondaryLeadOnly
holochronDissolutionRemainsSecondaryLead = refl

postDeathAssetDispositionTarget : Custody.EskridgeCorporateCustodyReverseTarget
postDeathAssetDispositionTarget = Custody.acquirePostDeathAssetDisposition

directorOfficerTransitionTarget : Custody.EskridgeCorporateCustodyReverseTarget
directorOfficerTransitionTarget = Custody.acquireDirectorOrOfficerTransition

repositoryOwnershipTarget : Custody.EskridgeCorporateCustodyReverseTarget
repositoryOwnershipTarget = Custody.acquireRepositoryOwnership

notebookCustodyTarget : Custody.EskridgeCorporateCustodyReverseTarget
notebookCustodyTarget = Custody.acquireNotebookCustody

applicationSuccessorTarget : App.AmyApplicationReverseTarget
applicationSuccessorTarget = App.acquireSuccessorOrHandover

record PostDeathTransitionSnowballBoundary : Set where
  constructor post-death-transition-snowball-boundary
  field
    laterCorporateObservationMayBeRetained : Bool
    laterCorporateObservationAutomaticallyClosesCustody : Bool
    dissolutionAutomaticallyIdentifiesSuccessor : Bool
    continuingInstituteStatusAutomaticallyIdentifiesSameApplicationCarrier : Bool
    officerTransitionAutomaticallyTransfersTechnicalIP : Bool
    successorHandoverRequiresSameCarrierEvidence : Bool
    corporateTransitionCreatesDeathCausation : Bool
    existingMissingDeceasedMatrixRemainsAuthoritative : Bool

open PostDeathTransitionSnowballBoundary public

canonicalPostDeathTransitionSnowballBoundary : PostDeathTransitionSnowballBoundary
canonicalPostDeathTransitionSnowballBoundary =
  post-death-transition-snowball-boundary true false false false false true false true
