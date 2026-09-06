module DASHI.Culture.RezaApplicationTransformationPossessionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ApplicationTransformationCapabilityBidiExact as T

-- Primary source:
-- Monica A. Jacinto and Dallis Ann Hardwick,
-- "Burn-resistant and high tensile strength metal alloys",
-- US20030053926A1 / US20040208777A1.

data PossessionStatus : Set where
  sourceBacked
  partial
  notLocated
  : PossessionStatus

record ApplicationRoleReceipt : Set where
  constructor application-role-receipt
  field
    roleOrPerson : String
    transformationCoordinates : List T.TransformationCoordinate
    status : PossessionStatus
    sourceReference : String
    boundedReading : String

open ApplicationRoleReceipt public

jacintoAlloyDesignRole : ApplicationRoleReceipt
jacintoAlloyDesignRole = application-role-receipt
  "Monica A. Jacinto"
  (T.constitutiveConfiguration ∷ T.sourceOrAlgorithmImplementation ∷ T.integrationWorkflow ∷ [])
  sourceBacked
  "US20030053926A1; US20040208777A1"
  "Named co-inventor on the alloy applications; the public patent discloses composition ranges, element-role reasoning, example performance and VIM/VAR plus mechanical-working process description."

rezaValidatedProcessWindowOwnership : ApplicationRoleReceipt
rezaValidatedProcessWindowOwnership = application-role-receipt
  "Monica Jacinto/Reza"
  (T.operatingWindow ∷ T.failureHistory ∷ T.qualificationEvidence ∷ T.tacitExecutionKnowledge ∷ [])
  notLocated
  "current bounded public patent/search record"
  "The patent does not close exact heat-treatment schedules, gamma-prime/grain-state tolerances, failed-batch history, flight/engine qualification evidence, or person-specific tacit manufacturing ownership."

record RezaApplicationBoundary : Set where
  constructor reza-application-boundary
  field
    coInventorImpliesSoleApplicationHolder : Bool
    coInventorImpliesSoleApplicationHolderIsFalse : coInventorImpliesSoleApplicationHolder ≡ false
    patentRecipeImpliesCompleteManufacturingCapability : Bool
    patentRecipeImpliesCompleteManufacturingCapabilityIsFalse : patentRecipeImpliesCompleteManufacturingCapability ≡ false
    constitutiveDesignRoleSourceBacked : Bool
    constitutiveDesignRoleSourceBackedIsTrue : constitutiveDesignRoleSourceBacked ≡ true
    validatedProcessWindowOwnershipClosed : Bool
    validatedProcessWindowOwnershipClosedIsFalse : validatedProcessWindowOwnershipClosed ≡ false

canonicalRezaApplicationBoundary : RezaApplicationBoundary
canonicalRezaApplicationBoundary = reza-application-boundary false refl false refl true refl false refl

data RezaApplicationReverseTarget : Set where
  acquireHeatTreatmentDevelopmentRecords
  acquireMicrostructureAcceptanceWindow
  acquireProcessToleranceAndFailureHistory
  acquireEngineQualificationOwnership
  acquireManufacturingHandover
  acquireSuccessorRole
  acquireRequalificationAfterDeparture
  : RezaApplicationReverseTarget
