module DASHI.Culture.LeBlancApplicationTransformationPossessionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ApplicationTransformationCapabilityBidiExact as T

-- NASA source:
-- "NASA 40 kW Fission Surface Power I and C Technology Development Path",
-- NTRS 20250008475 (2025), NASA peer reviewed, Public Use Permitted.
-- The recognition slide identifies Joshua LeBlanc as NASA SNP I&C TechMat Team Lead.

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

leblancTechMatRole : ApplicationRoleReceipt
leblancTechMatRole = application-role-receipt
  "Joshua LeBlanc / NASA SNP I&C TechMat Team Lead"
  (T.qualificationEvidence ∷ T.operatingWindow ∷ T.validationCorpus ∷ T.integrationWorkflow ∷ [])
  sourceBacked
  "NASA NTRS 20250008475, recognition slide"
  "The source names LeBlanc as the SNP I&C technology-maturation team lead; this supports a role in the maturation/qualification transformation, not sole ownership of every component/test/failure model."

leblancFailureMapOwnership : ApplicationRoleReceipt
leblancFailureMapOwnership = application-role-receipt
  "Joshua LeBlanc"
  (T.failureHistory ∷ T.uncertaintyModel ∷ T.calibrationState ∷ [])
  notLocated
  "current bounded NASA public record"
  "No public receipt in this pass establishes person-specific ownership of component failure envelopes, calibration-drift datasets, accelerated-life models, or system-level probability-of-failure analysis."

record LeBlancApplicationBoundary : Set where
  constructor leblanc-application-boundary
  field
    techMatLeadImpliesSoleQualificationOwner : Bool
    techMatLeadImpliesSoleQualificationOwnerIsFalse : techMatLeadImpliesSoleQualificationOwner ≡ false
    executiveCommitteeMembershipImpliesUniqueKnowledge : Bool
    executiveCommitteeMembershipImpliesUniqueKnowledgeIsFalse : executiveCommitteeMembershipImpliesUniqueKnowledge ≡ false
    technologyMaturationRoleSourceBacked : Bool
    technologyMaturationRoleSourceBackedIsTrue : technologyMaturationRoleSourceBacked ≡ true
    failureMapOwnershipClosed : Bool
    failureMapOwnershipClosedIsFalse : failureMapOwnershipClosed ≡ false

canonicalLeBlancApplicationBoundary : LeBlancApplicationBoundary
canonicalLeBlancApplicationBoundary = leblanc-application-boundary false refl false refl true refl false refl

data LeBlancApplicationReverseTarget : Set where
  acquireTechMatWorkBreakdown
  acquireQualificationTestOwnership
  acquireFailureEnvelopeOwnership
  acquireCalibrationDriftOwnership
  acquireSuccessorOrHandover
  acquireRequalificationDelayOrRework
  : LeBlancApplicationReverseTarget
