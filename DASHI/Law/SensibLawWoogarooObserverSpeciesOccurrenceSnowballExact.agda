module DASHI.Law.SensibLawWoogarooObserverSpeciesOccurrenceSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Observer-supplied occurrence evidence is a separate evidence fibre.
-- It can open acquisition/legal-consumer edges, but does not collapse into
-- expert validation, agency finding, exact GIS intersection, or statutory
-- conclusion.
------------------------------------------------------------------------

data OccurrencePlatform : Set where
  frogID : OccurrencePlatform
  iNaturalist : OccurrencePlatform
  googleMaps : OccurrencePlatform


data IdentificationStage : Set where
  observerSelected : IdentificationStage
  pendingValidation : IdentificationStage
  expertValidated : IdentificationStage
  communityIdentified : IdentificationStage
  agencyAccepted : IdentificationStage

record ObserverOccurrenceReceipt : Set where
  constructor observer-occurrence-receipt
  field
    platform : OccurrencePlatform
    nativeId : String
    observer : String
    dateTime : String
    waterBody : String
    selectedTaxon : String
    identificationStage : IdentificationStage
    locationReading : String
    attribution : String
    residual : String

open ObserverOccurrenceReceipt public

frog948283 : ObserverOccurrenceReceipt
frog948283 = observer-occurrence-receipt
  frogID
  "948283"
  "Johl Brown"
  "2026-09-05 16:39 QLD"
  "Stream or creek"
  "Adelotus brevis / Tusked Frog"
  pendingValidation
  "Native FrogID capture table supplied by the observer gives Lat -27.6502, Lng 152.9000. A separate observer-confirmed Google Maps point (-27.649945, 152.898928) remains a useful field-location cross-check, but the FrogID coordinate is now the platform-native location receipt."
  "Observer-supplied FrogID capture table; taxon remains observer-selected while the visible FrogID status is Pending - Submitted. Platform-native coordinate is source-paid separately from validator identity."
  "Acquire FrogID validator outcome; then perform an exact GIS join of the native point against Opossum/Woogaroo Creek, official corridor geometry, SHG habitat surfaces and project/clearing polygons."

frog948284 : ObserverOccurrenceReceipt
frog948284 = observer-occurrence-receipt
  frogID
  "948284"
  "Johl Brown"
  "2026-09-05 16:37 QLD"
  "Stream or creek"
  "taxon not independently source-paid in the supplied table/screenshot"
  pendingValidation
  "Native FrogID capture table supplied by the observer gives Lat -27.6499, Lng 152.8990. This is a distinct platform-native acoustic event approximately 2 minutes before 948283."
  "Observer-supplied FrogID capture table; do not transfer the 948283 Adelotus brevis selection to 948284 without its own taxon/result receipt."
  "Acquire the 948284 taxon/result and validator outcome; retain as a distinct acoustic capture even though the two points are nearby."

record NativePlatformCoordinateReceipt : Set where
  constructor native-platform-coordinate-receipt
  field
    platform : OccurrencePlatform
    nativeId : String
    latitude : String
    longitude : String
    provenance : String
    boundedReading : String

open NativePlatformCoordinateReceipt public

frog948283NativeCoordinate : NativePlatformCoordinateReceipt
frog948283NativeCoordinate = native-platform-coordinate-receipt
  frogID
  "948283"
  "-27.6502"
  "152.9000"
  "FrogID Captures Data Table supplied by the observer"
  "Platform-native coordinate for capture 948283; it is stronger than visual back-correlation but still requires a GIS intersection to establish relation to a legal parcel, habitat polygon or corridor boundary."

frog948284NativeCoordinate : NativePlatformCoordinateReceipt
frog948284NativeCoordinate = native-platform-coordinate-receipt
  frogID
  "948284"
  "-27.6499"
  "152.8990"
  "FrogID Captures Data Table supplied by the observer"
  "Platform-native coordinate for capture 948284; nearby location does not make it the same event or transfer the 948283 taxon selection."

record ObserverCoordinateReceipt : Set where
  constructor observer-coordinate-receipt
  field
    observer : String
    coordinate : String
    mapCarrier : String
    observerConfirmation : String
    boundedReading : String

open ObserverCoordinateReceipt public

opossumCreekObserverCoordinate : ObserverCoordinateReceipt
opossumCreekObserverCoordinate = observer-coordinate-receipt
  "Johl Brown"
  "-27.649945, 152.898928"
  "https://maps.app.goo.gl/8At3YCvNZCjg2Xzx8"
  "Observer states they personally confirm this point as where they were standing for the FrogID recordings."
  "Google Maps display plus first-person confirmation is retained as an independent field-location cross-check. Native FrogID coordinates are now separately available and take priority for platform-location claims."

record ObserverCollectionReceipt : Set where
  constructor observer-collection-receipt
  field
    platform : OccurrencePlatform
    observerHandle : String
    collectionLocator : String
    boundedReading : String

open ObserverCollectionReceipt public

johl1INaturalist : ObserverCollectionReceipt
johl1INaturalist = observer-collection-receipt
  iNaturalist
  "johl1"
  "https://www.inaturalist.org/observations?place_id=any&user_id=johl1&verifiable=any"
  "Public observation-search carrier supplied by the observer. Individual observations must be acquired and attributed separately."

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ObserverSelectionIsExpertValidation : Set where
data TwoCapturesAreTwoSpeciesConfirmations : Set where
data NearbyMapPinIsExactProjectIntersection : Set where
data VulnerableStatusPaysCriticalHabitat : Set where
data INaturalistCollectionPaysIndividualObservation : Set where
data FrogOccurrenceAutomaticallyPaysLegalTrigger : Set where
data ObserverConfirmedCoordinateIsNativeFrogIDCoordinate : Set where
data NativeFrogIDCoordinateIsSurveyGradeIntersection : Set where

data NativeCoordinateTransfersTaxonBetweenCaptures : Set where

noSelectionValidationCollapse : ObserverSelectionIsExpertValidation → ⊥
noSelectionValidationCollapse ()

noCaptureConfirmationCollapse : TwoCapturesAreTwoSpeciesConfirmations → ⊥
noCaptureConfirmationCollapse ()

noMapIntersectionCollapse : NearbyMapPinIsExactProjectIntersection → ⊥
noMapIntersectionCollapse ()

noStatusCriticalHabitatCollapse : VulnerableStatusPaysCriticalHabitat → ⊥
noStatusCriticalHabitatCollapse ()

noCollectionObservationCollapse : INaturalistCollectionPaysIndividualObservation → ⊥
noCollectionObservationCollapse ()

noOccurrenceLegalCollapse : FrogOccurrenceAutomaticallyPaysLegalTrigger → ⊥
noOccurrenceLegalCollapse ()

noObserverCoordinatePlatformCollapse : ObserverConfirmedCoordinateIsNativeFrogIDCoordinate → ⊥
noObserverCoordinatePlatformCollapse ()

noNativeCoordinateSurveyCollapse : NativeFrogIDCoordinateIsSurveyGradeIntersection → ⊥
noNativeCoordinateSurveyCollapse ()

noCoordinateTaxonTransfer : NativeCoordinateTransfersTaxonBetweenCaptures → ⊥
noCoordinateTaxonTransfer ()

record OccurrenceSnowballPolicy : Set where
  constructor occurrence-snowball-policy
  field
    preserveNativeCaptureId : Bool
    preserveObserverAttribution : Bool
    preserveValidationStage : Bool
    preserveDistinctCaptureEvents : Bool
    requireExactCoordinatesForSpatialJoin : Bool
    requireOwnTaxonReceiptPerCapture : Bool
    allowOccurrenceToOpenAcquisitionEdge : Bool
    prohibitAutomaticLegalPromotion : Bool
    distinguishObserverCoordinateFromPlatformCoordinate : Bool

canonicalOccurrenceSnowballPolicy : OccurrenceSnowballPolicy
canonicalOccurrenceSnowballPolicy = occurrence-snowball-policy
  true true true true true true true true true
