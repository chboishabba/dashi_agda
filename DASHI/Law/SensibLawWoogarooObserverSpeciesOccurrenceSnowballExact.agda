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
  "Observer confirms the recording location as -27.649945, 152.898928; supplied Google Maps screenshot displays that coordinate at the northern golf-course / Opossum Creek wooded interface. The coordinate is observer-confirmed, not yet a native FrogID coordinate export."
  "Observer-supplied FrogID capture plus separate observer-supplied Google Maps coordinate receipt; taxon remains observer-selected while the visible FrogID status is Pending - Submitted and validator comment is absent."
  "Acquire FrogID validator outcome and native FrogID coordinate/export; then perform exact GIS joins against the SHG 675 ha landscape, official corridor geometry and project/clearing polygons."

frog948284 : ObserverOccurrenceReceipt
frog948284 = observer-occurrence-receipt
  frogID
  "948284"
  "Johl Brown"
  "2026-09-05 16:37 QLD"
  "Stream or creek"
  "taxon not independently visible in supplied capture-detail screenshot"
  pendingValidation
  "User-supplied FrogID screenshot maps the capture essentially co-located with 948283. Observer confirms the same recording location as -27.649945, 152.898928; native FrogID coordinates remain to be acquired."
  "Observer-supplied FrogID capture plus separate observer location confirmation; do not transfer the 948283 taxon selection to 948284 without its own result receipt."
  "Acquire the 948284 result/selection, validator outcome and native coordinate/export; preserve it as a distinct acoustic event."

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
  "Google Maps display plus first-person confirmation supports the observer-location proposition; it is not yet the native FrogID platform coordinate and is not a survey-grade project/corridor intersection."

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

data ObserverConfirmedCoordinateIsSurveyGradeIntersection : Set where

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

noObserverCoordinateSurveyCollapse : ObserverConfirmedCoordinateIsSurveyGradeIntersection → ⊥
noObserverCoordinateSurveyCollapse ()

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
