module DASHI.Empirical.GoogleTimelineSpacetimeBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.SpacetimeHistoryWorldTube
open import DASHI.Biology.IntersectionalLongitudinalResidualDynamics
  using
    ( IntersectionalAxis
    ; IntersectionalResidualCarrier
    ; mkIntersectionalResidualCarrierOf
    )

------------------------------------------------------------------------
-- Empirical bridge from a Google Maps Timeline-style export into the typed
-- spacetime-history carrier.
--
-- This module does not parse a vendor schema.  It specifies the normalized
-- receipt expected from any importer and connects place/time observations to
-- the existing DASHI longitudinal body × time × place × relation × institution
-- × axis-bundle carrier.  Vendor inference is retained as provenance and never
-- promoted to exact location or a complete account of lived experience.

data ImportFieldKind : Set where
  latitudeField : ImportFieldKind
  longitudeField : ImportFieldKind
  altitudeField : ImportFieldKind
  timestampField : ImportFieldKind
  accuracyField : ImportFieldKind
  activityField : ImportFieldKind
  placeLabelField : ImportFieldKind
  sourceField : ImportFieldKind

data ImportStatus : Set where
  importedStatus : ImportStatus
  missingStatus : ImportStatus
  inferredStatus : ImportStatus
  rejectedStatus : ImportStatus

record TimelineImportReceipt : Set where
  constructor mkTimelineImportReceipt
  field
    receiptRowIndex : Nat
    receiptTimestamp : Nat
    receiptPlaceLabel : String
    receiptCoordinateReference : String
    receiptEastCoordinate : Nat
    receiptNorthCoordinate : Nat
    receiptAltitudeCoordinate : Nat
    receiptAccuracyRadius : Nat
    receiptMotionMode : MotionMode
    receiptSource : String
    receiptStatus : ImportStatus
    receiptVendorInference : Bool
    receiptExactPositionClaim : Bool
    receiptExactPositionClaimIsFalse : receiptExactPositionClaim ≡ false
open TimelineImportReceipt public

mkTimelineImportReceiptOf :
  Nat → Nat → String → String → Nat → Nat → Nat → Nat → MotionMode →
  String → ImportStatus → Bool → TimelineImportReceipt
mkTimelineImportReceiptOf
  index time place coordinateReference east north altitude accuracy mode source status inferred =
  mkTimelineImportReceipt
    index time place coordinateReference east north altitude accuracy mode source status inferred false refl

receiptPosition : TimelineImportReceipt → SpatialSample
receiptPosition receipt =
  mkSpatialSample
    (receiptEastCoordinate receipt)
    (receiptNorthCoordinate receipt)
    (receiptAltitudeCoordinate receipt)
    (receiptCoordinateReference receipt)

receiptObservation : TimelineImportReceipt → TimelineObservation
receiptObservation receipt =
  mkUncertainTimelineObservation
    (receiptRowIndex receipt)
    (receiptTimestamp receipt)
    (receiptPlaceLabel receipt)
    (receiptPosition receipt)
    (receiptAccuracyRadius receipt)
    (receiptMotionMode receipt)
    (receiptSource receipt)

record TimelineSemanticContext : Set where
  constructor mkTimelineSemanticContext
  field
    contextBody : String
    contextRelation : String
    contextInstitution : String
    contextAxes : List IntersectionalAxis
    contextReading : String
open TimelineSemanticContext public

receiptLongitudinalCarrier :
  TimelineSemanticContext →
  TimelineImportReceipt →
  IntersectionalResidualCarrier
receiptLongitudinalCarrier context receipt =
  mkIntersectionalResidualCarrierOf
    (contextBody context)
    (receiptTimestamp receipt)
    (receiptPlaceLabel receipt)
    (contextRelation context)
    (contextInstitution context)
    (contextAxes context)
    (contextReading context)

record IntegratedTimelineRow : Set where
  constructor mkIntegratedTimelineRow
  field
    integratedReceipt : TimelineImportReceipt
    integratedObservation : TimelineObservation
    integratedLongitudinalCarrier : IntersectionalResidualCarrier
    integratedWorldTubeSection : WorldTubeSection
    integratedVendorInferenceIsNotExperience : Bool
    integratedVendorInferenceIsNotExperienceIsTrue :
      integratedVendorInferenceIsNotExperience ≡ true
open IntegratedTimelineRow public

integrateTimelineRow :
  TimelineSemanticContext →
  Nat →
  Nat →
  TimelineImportReceipt →
  IntegratedTimelineRow
integrateTimelineRow context temporalThickness meaningWeight receipt =
  mkIntegratedTimelineRow
    receipt
    observation
    (receiptLongitudinalCarrier context receipt)
    (mkWorldTubeSection
      observation
      (receiptAccuracyRadius receipt)
      temporalThickness
      meaningWeight)
    true
    refl
  where
    observation : TimelineObservation
    observation = receiptObservation receipt

record TimelineDatasetReceipt : Set where
  constructor mkTimelineDatasetReceipt
  field
    datasetName : String
    datasetRows : List IntegratedTimelineRow
    datasetMissingRowsAcknowledged : Bool
    datasetMissingRowsAcknowledgedIsTrue :
      datasetMissingRowsAcknowledged ≡ true
    datasetCompleteExperienceClaim : Bool
    datasetCompleteExperienceClaimIsFalse :
      datasetCompleteExperienceClaim ≡ false
    datasetAuthorityClaim : Bool
    datasetAuthorityClaimIsFalse : datasetAuthorityClaim ≡ false
open TimelineDatasetReceipt public

mkTimelineDatasetReceiptOf :
  String → List IntegratedTimelineRow → TimelineDatasetReceipt
mkTimelineDatasetReceiptOf name rows =
  mkTimelineDatasetReceipt name rows true refl false refl false refl

canonicalImportFields : List ImportFieldKind
canonicalImportFields =
  latitudeField
  ∷ longitudeField
  ∷ altitudeField
  ∷ timestampField
  ∷ accuracyField
  ∷ activityField
  ∷ placeLabelField
  ∷ sourceField
  ∷ []

canonicalTimelineBridgeNotes : List String
canonicalTimelineBridgeNotes =
  "Vendor rows are normalized into uncertain observations before geometry is built"
  ∷ "Time and place feed the existing longitudinal DASHI carrier"
  ∷ "Body, relation, institution, and axis bundle remain explicit semantic context"
  ∷ "Accuracy radius becomes world-tube thickness rather than false precision"
  ∷ "Activity labels are provenance-bearing inferences, not ground truth"
  ∷ "Missing samples are acknowledged at dataset level"
  ∷ "A mobility history is neither a complete life history nor surveillance authority"
  ∷ []
