module DASHI.Core.ApplicationCapabilityCustodyBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- APPLICATION CAPABILITY CUSTODY, BIDI
--
-- A capability can be scientifically public yet operationally distributed
-- across physical apparatus, data, code, IP, credentials and organisational
-- control.  Custody is separate from authorship, expertise and causal event
-- hypotheses.
------------------------------------------------------------------------

data CustodyCoordinate : Set where
  physicalApparatus : CustodyCoordinate
  rawData : CustodyCoordinate
  reducedData : CustodyCoordinate
  sourceRepository : CustodyCoordinate
  calibrationArchive : CustodyCoordinate
  configurationArchive : CustodyCoordinate
  qualificationArchive : CustodyCoordinate
  failureHistory : CustodyCoordinate
  notebooks : CustodyCoordinate
  intellectualProperty : CustodyCoordinate
  accessCredential : CustodyCoordinate
  facilityAccess : CustodyCoordinate
  supplierRelationship : CustodyCoordinate


data CustodyState : Set where
  publicCustody : CustodyState
  institutionalCustody : CustodyState
  crossInstitutionalCustody : CustodyState
  privateCustody : CustodyState
  distributedCustody : CustodyState
  custodyUnknown : CustodyState


record CapabilityCustodyReceipt : Set where
  constructor capability-custody-receipt
  field
    application : String
    coordinate : CustodyCoordinate
    state : CustodyState
    custodian : String
    sourceReference : String
    boundedReading : String

open CapabilityCustodyReceipt public

record AccessContinuityReceipt : Set where
  constructor access-continuity-receipt
  field
    application : String
    priorRole : String
    laterRole : String
    sameCarrier : Bool
    continuityReference : String
    boundedReading : String

open AccessContinuityReceipt public

record CustodyBoundary : Set where
  constructor custody-boundary
  field
    namedAuthorImpliesPhysicalCustody : Bool
    namedAuthorImpliesPhysicalCustodyIsFalse : namedAuthorImpliesPhysicalCustody ≡ false
    projectContinuationImpliesSameCalibrationState : Bool
    projectContinuationImpliesSameCalibrationStateIsFalse : projectContinuationImpliesSameCalibrationState ≡ false
    externalApparatusCustodyImpliesNoJPLSpecificKnowHow : Bool
    externalApparatusCustodyImpliesNoJPLSpecificKnowHowIsFalse : externalApparatusCustodyImpliesNoJPLSpecificKnowHow ≡ false
    corporateRoleImpliesPostAcquisitionAccess : Bool
    corporateRoleImpliesPostAcquisitionAccessIsFalse : corporateRoleImpliesPostAcquisitionAccess ≡ false
    formerInstitutionalRoleImpliesEventTimeAccess : Bool
    formerInstitutionalRoleImpliesEventTimeAccessIsFalse : formerInstitutionalRoleImpliesEventTimeAccess ≡ false

canonicalCustodyBoundary : CustodyBoundary
canonicalCustodyBoundary = custody-boundary false refl false refl false refl false refl false refl

data CustodyReverseTarget : Set where
  acquirePhysicalCustody : CustodyReverseTarget
  acquireRepositoryCustody : CustodyReverseTarget
  acquireCalibrationArchiveCustody : CustodyReverseTarget
  acquireConfigurationArchiveCustody : CustodyReverseTarget
  acquireIPOwnership : CustodyReverseTarget
  acquireAccessCredentialHistory : CustodyReverseTarget
  acquireFacilityAccessHistory : CustodyReverseTarget
  acquirePostTransitionRole : CustodyReverseTarget
  acquireSameCarrierTransfer : CustodyReverseTarget
