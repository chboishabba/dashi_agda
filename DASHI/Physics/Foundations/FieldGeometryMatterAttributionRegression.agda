{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.FieldGeometryMatterAttributionRegression where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Physics.Foundations.PhysicalResidualPromotionExact as Residual
import DASHI.Physics.Foundations.CausalTransportFTLObligationsExact as FTL

------------------------------------------------------------------------
-- ATTRIBUTION / AUTHORITY REGRESSION
--
-- External evidence may populate source-bounded coordinates.  It does not
-- become ownership of DASHI synthesis, and weak evidence classes cannot pay
-- stronger physical promotion simply by appearing in the same graph.
------------------------------------------------------------------------

data PhysicalEvidenceClass : Set where
  measuredObservation : PhysicalEvidenceClass
  calibratedMeasurement : PhysicalEvidenceClass
  simulationExperimentComparison : PhysicalEvidenceClass
  analyticTheory : PhysicalEvidenceClass
  fittedModel : PhysicalEvidenceClass
  plannedMeasurement : PhysicalEvidenceClass
  vendorClaim : PhysicalEvidenceClass
  historicalNarrativeClaim : PhysicalEvidenceClass
  speculativeConsumer : PhysicalEvidenceClass
  repositoryTheorem : PhysicalEvidenceClass

record EvidencePaymentReceipt : Set where
  constructor evidence-payment-receipt
  field
    evidenceClass : PhysicalEvidenceClass
    sourceReference : String
    boundedClaim : String
    sameObjectStatus : String
    acceptedByConsumer : Bool
    createsGenericDASHITheoremOwnership : Bool

open EvidencePaymentReceipt public

canonicalSourceBoundedReceipt : EvidencePaymentReceipt
canonicalSourceBoundedReceipt =
  evidence-payment-receipt
    measuredObservation
    "external source object"
    "only the proposition directly established by the source"
    "same-object status must be stated separately"
    true
    false

------------------------------------------------------------------------
-- No constructors: these promotions cannot be obtained from the named weak
-- evidence class alone.  A stronger domain owner must provide its own receipt.
------------------------------------------------------------------------

data VendorClaimPhysicalValidationPermission : Set where
data PlannedMeasurementCalibrationPermission : Set where
data HistoricalAssociationMechanismPermission : Set where
data SciFiScientificAuthorityPermission : Set where
data ExternalSourceDASHISynthesisOwnershipPermission : Set where

record AttributionRegressionBoundary : Set where
  constructor attribution-regression-boundary
  field
    sourceMetadataDoesNotCreateTruth : Bool
    citationDoesNotImportProof : Bool
    externalSourceDoesNotOwnDASHISynthesis : Bool
    vendorClaimDoesNotPayPhysicalValidation : Bool
    plannedMeasurementDoesNotPayCalibration : Bool
    historicalAssociationDoesNotPayMechanism : Bool
    scifiDoesNotPayScientificAuthority : Bool
    theoremShapeTransferDoesNotTransferMechanism : Bool
    theoremShapeTransferDoesNotTransferCalibration : Bool
    theoremShapeTransferDoesNotTransferEmpiricalValues : Bool
    theoremShapeTransferDoesNotTransferHistoricalIntent : Bool

open AttributionRegressionBoundary public

canonicalAttributionRegressionBoundary : AttributionRegressionBoundary
canonicalAttributionRegressionBoundary =
  attribution-regression-boundary
    true true true true true true true true true true true

attributedSourceCoreReceiptStillNonPromoting :
  GenericReceipt.promotesClaim Attribution.canonicalAttributedSourceCoreReceipt
    ≡ false
attributedSourceCoreReceiptStillNonPromoting =
  Attribution.canonicalAttributedSourceCoreReceiptNonPromoting

residualPromotionBoundaryReused : Residual.ResidualPromotionBoundary
residualPromotionBoundaryReused = Residual.canonicalResidualPromotionBoundary

scifiBoundaryReused : FTL.SciFiConsumerBoundary
scifiBoundaryReused = FTL.canonicalSciFiBoundary
