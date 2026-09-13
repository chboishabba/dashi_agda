module DASHI.Culture.AmyEskridgePOAMSApplicationCustodySnowballWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.KnowledgeObjectLineageBidiExact as LineageCore
import DASHI.Core.LayeredKnowledgeReleaseBidiExact as ReleaseCore
import DASHI.Culture.AmyEskridgePOAMSBoundaryCandidateExact as Candidate
import DASHI.Culture.AmyEskridgePOAMSObjectLineageExact as Lineage
import DASHI.Culture.POAMSLayeredReleaseExact as Release
import DASHI.Culture.AmyEskridgeApplicationTransformationExact as App
import DASHI.Culture.AmyEskridgeCorporateCustodySurfaceExact as Custody
import DASHI.Culture.MissingDeceasedOverlookedDimensionMatrixExact as Matrix
import DASHI.Culture.MissingDeceasedFullApplicationTransformationAtlasExact as Atlas

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: POAMS / APPLICATION / CUSTODY SNOWBALL WELD
--
-- Existing owners already contain the relevant objects and boundaries. This
-- adapter composes them so the Amy investigation consumes the accumulated
-- POAMS lineage without collapsing study, report, review object, private
-- derivative, data, hardware, or successor/custody into one object.
------------------------------------------------------------------------

poamsReviewToTMRemainsCandidateIdentity :
  LineageCore.relation Lineage.reviewToTMStrongCandidate ≡ LineageCore.candidateSameObject
poamsReviewToTMRemainsCandidateIdentity = refl

poamsCandidateStillStrongNotExact :
  Candidate.poamsExactSameObjectEstablished Candidate.canonicalCurrentPOAMSCandidateAssessment ≡ false
poamsCandidateStillStrongNotExact = refl

poamsPublicReportIsPublic :
  ReleaseCore.state Release.poamsPublicReport ≡ ReleaseCore.publicState
poamsPublicReportIsPublic = refl

poamsUnderlyingDataRemainPrivateCustody :
  ReleaseCore.state Release.poamsData ≡ ReleaseCore.privateCustody
poamsUnderlyingDataRemainPrivateCustody = refl

poamsHardwareRemainsPrivateCustody :
  ReleaseCore.state Release.poamsHardware ≡ ReleaseCore.privateCustody
poamsHardwareRemainsPrivateCustody = refl

poamsInstituteDerivativeReleaseStateStillUnknown :
  ReleaseCore.state Release.poamsPrivateDerivatives ≡ ReleaseCore.unknown
poamsInstituteDerivativeReleaseStateStillUnknown = refl

amyApplicationFirstMissingLeafStillDerivedObjectIdentity :
  App.firstAmyApplicationMissingLeaf ≡ App.acquireInstituteDerivedObjectIdentity
amyApplicationFirstMissingLeafStillDerivedObjectIdentity = refl

amyMissingDeceasedCustodyStillOpen :
  Matrix.physicalOrDataCustody Matrix.eskridgeRow ≡ Matrix.open
amyMissingDeceasedCustodyStillOpen = refl

amyAtlasNonPublicResidualStillPartial :
  Atlas.nonPublicResidualStatus Atlas.amyEskridgeRow ≡ Atlas.atlasPartial
amyAtlasNonPublicResidualStillPartial = refl

amyAtlasSuccessionStillNotLocated :
  Atlas.successionStatus Atlas.amyEskridgeRow ≡ Atlas.atlasNotLocated
amyAtlasSuccessionStillNotLocated = refl

repositoryOwnershipTarget : Custody.EskridgeCorporateCustodyReverseTarget
repositoryOwnershipTarget = Custody.acquireRepositoryOwnership

apparatusCustodyTarget : Custody.EskridgeCorporateCustodyReverseTarget
apparatusCustodyTarget = Custody.acquireApparatusTitleAndLocation

notebookCustodyTarget : Custody.EskridgeCorporateCustodyReverseTarget
notebookCustodyTarget = Custody.acquireNotebookCustody

postDeathDispositionTarget : Custody.EskridgeCorporateCustodyReverseTarget
postDeathDispositionTarget = Custody.acquirePostDeathAssetDisposition

successorHandoverTarget : App.AmyApplicationReverseTarget
successorHandoverTarget = App.acquireSuccessorOrHandover

record POAMSApplicationCustodyBoundary : Set where
  constructor poams-application-custody-boundary
  field
    publicTMEqualsUnderlyingData : Bool
    publicTMEqualsPhysicalHardware : Bool
    publicTMEqualsInstituteDerivative : Bool
    strongCandidateIdentityEqualsExactIdentity : Bool
    privateQuantumMachinesCustodyEqualsInstituteCustody : Bool
    institutePrivateMaturationEqualsExactDerivativeIdentity : Bool
    publicFoundationPaysApplicationTransformation : Bool
    applicationTransformationPaysSuccessorHandover : Bool
    layeredReleaseMayRefineCustodySearch : Bool
    accumulatedPOAMSEvidenceMayBeRetainedBeforeExactIdentity : Bool
    exactIdentityAndCustodyRemainConsumerSpecific : Bool
    applicationCriticalityCreatesDeathCausation : Bool

open POAMSApplicationCustodyBoundary public

canonicalPOAMSApplicationCustodyBoundary : POAMSApplicationCustodyBoundary
canonicalPOAMSApplicationCustodyBoundary =
  poams-application-custody-boundary
    false false false false false false false false true true true false

------------------------------------------------------------------------
-- Highest-alpha interpretation of the accumulated repo state:
--
--  * POAMS public foundation is paid as a source-backed public object;
--  * V5 data/hardware private custody is paid for the NASA/QM programme;
--  * Amy's later Institute maturation is source-attributed as a distinct object;
--  * the exact Institute derivative identity and successor/handover remain the
--    first same-object application/custody residuals.
------------------------------------------------------------------------

record CurrentComposedPOAMSFrontier : Set where
  constructor current-composed-poams-frontier
  field
    publicFoundationPaid : Bool
    documentedPartialReleasePaid : Bool
    amyPrivateMaturationAttributed : Bool
    exactInstituteDerivativeIdentityPaid : Bool
    instituteApparatusCustodyPaid : Bool
    instituteRepositoryCustodyPaid : Bool
    instituteNotebookCustodyPaid : Bool
    successorHandoverPaid : Bool
    eventCausalLinkPaid : Bool

open CurrentComposedPOAMSFrontier public

currentComposedPOAMSFrontier : CurrentComposedPOAMSFrontier
currentComposedPOAMSFrontier =
  current-composed-poams-frontier true true true false false false false false false
