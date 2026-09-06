module DASHI.Core.DistributedApplicationSurfaceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

data DistributionSurface : Set where
  multiAuthorPublication
  multiLabProgramme
  multiLeadOrganisation
  documentedProcedure
  sharedDatabase
  configurationManagement
  successorRole
  crossTrainedTeam
  : DistributionSurface

data CarrierDistributionStatus : Set where
  distributedSourceBacked
  concentratedSourceBacked
  mixedOrPartial
  notLocated
  : CarrierDistributionStatus

record CarrierDistributionReceipt : Set where
  constructor carrier-distribution-receipt
  field
    application : String
    carrierName : String
    visibleSurfaces : List DistributionSurface
    status : CarrierDistributionStatus
    sourceReference : String
    boundedReading : String

open CarrierDistributionReceipt public

record DistributionBoundary : Set where
  constructor distribution-boundary
  field
    multiAuthorImpliesCarrierDistributed : Bool
    multiAuthorImpliesCarrierDistributedIsFalse : multiAuthorImpliesCarrierDistributed ≡ false
    multiLabImpliesEveryCarrierDistributed : Bool
    multiLabImpliesEveryCarrierDistributedIsFalse : multiLabImpliesEveryCarrierDistributed ≡ false
    documentedProcedureImpliesNoTacitResidual : Bool
    documentedProcedureImpliesNoTacitResidualIsFalse : documentedProcedureImpliesNoTacitResidual ≡ false
    seniorRoleImpliesCarrierConcentrated : Bool
    seniorRoleImpliesCarrierConcentratedIsFalse : seniorRoleImpliesCarrierConcentrated ≡ false
    carrierDistributionRequiresSameObjectEvidence : Bool
    carrierDistributionRequiresSameObjectEvidenceIsTrue : carrierDistributionRequiresSameObjectEvidence ≡ true

canonicalDistributionBoundary : DistributionBoundary
canonicalDistributionBoundary = distribution-boundary false refl false refl false refl false refl true refl

data DistributionReverseTarget : Set where
  acquireTaskAllocation
  acquireAccessRoster
  acquireConfigurationOwnership
  acquireCrossTraining
  acquireHandoverRecord
  acquireSuccessorIdentity
  acquireProcedureCoverage
  acquireTacitResidualEvidence
  acquirePostDepartureRework
  : DistributionReverseTarget
