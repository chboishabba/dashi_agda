module DASHI.Physics.Closure.ClaimGovernancePromotionObligation where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.TemporalSheafProofObligations as Temporal

------------------------------------------------------------------------
-- W7n claim-governance promotion obligation.
--
-- This module is deliberately non-promoting.  It names the typed receipt
-- surface required before higher-structure, cross-scale, temporal, spacetime,
-- neurochemical, or market readings can be treated as governed claims.  It
-- does not prove any temporal/sheaf/spacetime/biomedical/market theorem.

data ClaimGovernancePromotionAuthorityToken : Set where

data GovernedReadingLane : Set where
  higherStructureReading :
    GovernedReadingLane
  crossScaleReading :
    GovernedReadingLane
  temporalSheafReading :
    GovernedReadingLane
  spacetimeSheafReading :
    GovernedReadingLane
  neurochemicalReading :
    GovernedReadingLane
  marketReading :
    GovernedReadingLane

record ClaimGovernanceValidationFields : Setω where
  field
    higherStructureCarrier :
      Set

    crossScaleCarrier :
      Set

    neurochemicalCarrier :
      Set

    marketCarrier :
      Set

    temporalStateSpaceReceipt :
      Temporal.TemporalStateSpaceReceipt

    spacetimeStateSpaceReceipt :
      Temporal.SpacetimeStateSpaceReceipt

    higherStructureValidation :
      higherStructureCarrier →
      Set

    crossScaleValidation :
      crossScaleCarrier →
      Set

    neurochemicalValidation :
      neurochemicalCarrier →
      Set

    marketValidation :
      marketCarrier →
      Set

    temporalGovernanceValidation :
      Temporal.TemporalStateSpaceReceipt →
      Set

    spacetimeGovernanceValidation :
      Temporal.SpacetimeStateSpaceReceipt →
      Set

    noPromotionBoundary :
      List String

record ClaimGovernancePromotionReceipt : Setω where
  field
    authorityToken :
      ClaimGovernancePromotionAuthorityToken

    validationFields :
      ClaimGovernanceValidationFields

    governedLane :
      GovernedReadingLane →
      Set

    validatesHigherStructure :
      (x :
        ClaimGovernanceValidationFields.higherStructureCarrier
          validationFields) →
      ClaimGovernanceValidationFields.higherStructureValidation
        validationFields
        x

    validatesCrossScale :
      (x :
        ClaimGovernanceValidationFields.crossScaleCarrier
          validationFields) →
      ClaimGovernanceValidationFields.crossScaleValidation
        validationFields
        x

    validatesNeurochemical :
      (x :
        ClaimGovernanceValidationFields.neurochemicalCarrier
          validationFields) →
      ClaimGovernanceValidationFields.neurochemicalValidation
        validationFields
        x

    validatesMarket :
      (x :
        ClaimGovernanceValidationFields.marketCarrier
          validationFields) →
      ClaimGovernanceValidationFields.marketValidation
        validationFields
        x

    validatesTemporalSheaf :
      ClaimGovernanceValidationFields.temporalGovernanceValidation
        validationFields
        (ClaimGovernanceValidationFields.temporalStateSpaceReceipt
          validationFields)

    validatesSpacetimeSheaf :
      ClaimGovernanceValidationFields.spacetimeGovernanceValidation
        validationFields
        (ClaimGovernanceValidationFields.spacetimeStateSpaceReceipt
          validationFields)

------------------------------------------------------------------------
-- Current obligations-needed diagnostic.

data ClaimGovernanceMissingField : Set where
  missingPromotionAuthorityToken :
    ClaimGovernanceMissingField
  missingHigherStructureValidation :
    ClaimGovernanceMissingField
  missingCrossScaleValidation :
    ClaimGovernanceMissingField
  missingTemporalSheafReceipt :
    ClaimGovernanceMissingField
  missingSpacetimeSheafReceipt :
    ClaimGovernanceMissingField
  missingNeurochemicalValidation :
    ClaimGovernanceMissingField
  missingMarketValidation :
    ClaimGovernanceMissingField
  missingClaimBoundaryPolicy :
    ClaimGovernanceMissingField

data ClaimGovernanceCurrentStatus : Set where
  claimGovernanceObligationOnly :
    ClaimGovernanceCurrentStatus
  promotionAuthorityBlocked :
    ClaimGovernanceCurrentStatus
  validationReceiptsBlocked :
    ClaimGovernanceCurrentStatus
  nonPromotingDiagnostic :
    ClaimGovernanceCurrentStatus

record ClaimGovernancePromotionCurrentStatus : Setω where
  field
    currentStatus :
      ClaimGovernanceCurrentStatus

    coveredReadingLanes :
      List GovernedReadingLane

    missingFields :
      List ClaimGovernanceMissingField

    temporalImportBoundary :
      String

    requiredNextReceipt :
      String

    noAuthorityConstructedHere :
      List String

    noPromotionBoundary :
      List String

canonicalClaimGovernancePromotionCurrentStatus :
  ClaimGovernancePromotionCurrentStatus
canonicalClaimGovernancePromotionCurrentStatus =
  record
    { currentStatus =
        nonPromotingDiagnostic
    ; coveredReadingLanes =
        higherStructureReading
        ∷ crossScaleReading
        ∷ temporalSheafReading
        ∷ spacetimeSheafReading
        ∷ neurochemicalReading
        ∷ marketReading
        ∷ []
    ; missingFields =
        missingPromotionAuthorityToken
        ∷ missingHigherStructureValidation
        ∷ missingCrossScaleValidation
        ∷ missingTemporalSheafReceipt
        ∷ missingSpacetimeSheafReceipt
        ∷ missingNeurochemicalValidation
        ∷ missingMarketValidation
        ∷ missingClaimBoundaryPolicy
        ∷ []
    ; temporalImportBoundary =
        "TemporalSheafProofObligations is imported only as an obligation surface"
    ; requiredNextReceipt =
        "provide authority plus validation receipts before promoting higher-structure, cross-scale, temporal, spacetime, neurochemical, or market readings"
    ; noAuthorityConstructedHere =
        "ClaimGovernancePromotionAuthorityToken has no constructor in this module"
        ∷ "This module does not inhabit ClaimGovernancePromotionReceipt"
        ∷ []
    ; noPromotionBoundary =
        "This module is a W7 claim-governance obligation surface only"
        ∷ "No temporal sheaf theorem is asserted here"
        ∷ "No spacetime theorem is asserted here"
        ∷ "No biomedical or neurochemical theorem is asserted here"
        ∷ "No market theorem or trading-signal theorem is asserted here"
        ∷ "No higher-structure or cross-scale reading is promoted here"
        ∷ []
    }

canonicalClaimGovernanceMissingFields :
  List ClaimGovernanceMissingField
canonicalClaimGovernanceMissingFields =
  ClaimGovernancePromotionCurrentStatus.missingFields
    canonicalClaimGovernancePromotionCurrentStatus
