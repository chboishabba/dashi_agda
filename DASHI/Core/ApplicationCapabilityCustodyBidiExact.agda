module DASHI.Core.ApplicationCapabilityCustodyBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

data CustodyCoordinate : Set where
  physicalApparatus rawData reducedData sourceRepository calibrationArchive
  configurationArchive qualificationArchive failureHistory notebooks
  intellectualProperty accessCredential facilityAccess supplierRelationship
  : CustodyCoordinate

data CustodyState : Set where
  publicCustody institutionalCustody crossInstitutionalCustody privateCustody
  distributedCustody custodyUnknown : CustodyState

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
  acquirePhysicalCustody acquireRepositoryCustody acquireCalibrationArchiveCustody
  acquireConfigurationArchiveCustody acquireIPOwnership acquireAccessCredentialHistory
  acquireFacilityAccessHistory acquirePostTransitionRole acquireSameCarrierTransfer
  : CustodyReverseTarget
