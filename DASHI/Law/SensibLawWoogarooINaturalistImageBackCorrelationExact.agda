module DASHI.Law.SensibLawWoogarooINaturalistImageBackCorrelationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Image-backed spatial correlation for observer occurrence evidence.
--
-- This owner deliberately introduces an intermediate spatial-evidence tier:
-- saved locality labels + user-supplied profile/map/satellite screenshots can
-- support a same-neighbourhood proposition without pretending to recover the
-- native observation coordinate or an exact GIS intersection.
------------------------------------------------------------------------

data SpatialEvidenceTier : Set where
  localityLabelOnly : SpatialEvidenceTier
  imageBackCorrelatedNeighbourhood : SpatialEvidenceTier
  observerConfirmedCoordinate : SpatialEvidenceTier
  nativePlatformCoordinate : SpatialEvidenceTier
  exactGISIntersection : SpatialEvidenceTier

record ImageBackCorrelationReceipt : Set where
  constructor image-back-correlation-receipt
  field
    nativeId : String
    taxonReading : String
    savedLocality : String
    tier : SpatialEvidenceTier
    imageReading : String
    boundedInference : String
    residual : String

open ImageBackCorrelationReceipt public

zanda357433327BackCorrelation : ImageBackCorrelationReceipt
zanda357433327BackCorrelation = image-back-correlation-receipt
  "357433327"
  "Zanda / Yellow-tailed and White-tailed Black Cockatoos; Needs ID"
  "Brookwater Dr at Greg Norman Circuit, Brookwater QLD 4300"
  imageBackCorrelatedNeighbourhood
  "The observer-supplied iNaturalist profile map shows a dense observation cluster in Brookwater immediately west of Springfield. Separate observer-supplied satellite imagery identifies the Opossum Creek / northern golf-course wooded interface in the same Brookwater landscape."
  "The saved locality plus the map screenshots support same Brookwater/Opossum-corridor neighbourhood. They do not identify which rendered iNaturalist pin belongs to observation 357433327 and do not establish an exact project or creek intersection."
  "Acquire the native iNaturalist observation coordinate/accuracy or an individual observation-page map before promoting beyond neighbourhood correlation."

calomela388681275BackCorrelation : ImageBackCorrelationReceipt
calomela388681275BackCorrelation = image-back-correlation-receipt
  "388681275"
  "Calomela juncta; Research Grade"
  "Brookwater Dr at Greg Norman Circuit, Brookwater QLD 4300"
  imageBackCorrelatedNeighbourhood
  "The saved locality matches the dense Brookwater cluster visible on the observer-supplied iNaturalist profile map; the supplied satellite/Opossum images independently anchor that neighbourhood against the wooded Opossum Creek / golf-course edge."
  "Supports same-neighbourhood biodiversity context only; Research Grade improves taxon confidence but does not make the image-level spatial correlation exact."
  "Acquire native coordinate/accuracy if this record is used in a corridor or project intersection analysis."

scarlet364188331BackCorrelation : ImageBackCorrelationReceipt
scarlet364188331BackCorrelation = image-back-correlation-receipt
  "364188331"
  "Myzomela sanguinolenta / Scarlet Honeyeater; Research Grade"
  "Brookwater QLD 4300"
  localityLabelOnly
  "The profile map contains multiple Brookwater observations, but the broader saved locality does not distinguish the Opossum/golf-course cluster from other Brookwater points."
  "Retain as broader Brookwater landscape context; do not back-assign it to the Opossum cluster from the profile-map screenshot alone."
  "Acquire native coordinate/accuracy or an observation-specific map."

frog948283ExactObserverCoordinate : ImageBackCorrelationReceipt
frog948283ExactObserverCoordinate = image-back-correlation-receipt
  "FrogID 948283"
  "Adelotus brevis / Tusked Frog; observer-selected, FrogID pending validation"
  "observer-confirmed standing point"
  observerConfirmedCoordinate
  "Observer-supplied Google Maps share displays -27.649945, 152.898928. Satellite imagery and FrogID map screenshots visually agree with the northern golf-course / Opossum Creek wooded interface, and the observer personally confirms that point as the recording location."
  "This pays the observer-location proposition at -27.649945, 152.898928. It is stronger than neighbourhood correlation but remains distinct from a native FrogID coordinate export, survey-grade location, expert taxon validation or legal GIS intersection."
  "Acquire FrogID validator outcome and native coordinate/export; then join against SHG 675 ha, corridor and project/clearing polygons."

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data DenseProfileClusterIdentifiesNativePin : Set where

data SavedStreetLocalityIsExactCoordinate : Set where

data ImageNeighbourhoodIsGISIntersection : Set where

data ObserverCoordinateIsNativePlatformCoordinate : Set where

data SameNeighbourhoodIsSameObservationPoint : Set where

noClusterPinCollapse : DenseProfileClusterIdentifiesNativePin → ⊥
noClusterPinCollapse ()

noStreetCoordinateCollapse : SavedStreetLocalityIsExactCoordinate → ⊥
noStreetCoordinateCollapse ()

noImageGISCollapse : ImageNeighbourhoodIsGISIntersection → ⊥
noImageGISCollapse ()

noObserverNativeCollapse : ObserverCoordinateIsNativePlatformCoordinate → ⊥
noObserverNativeCollapse ()

noNeighbourhoodPointCollapse : SameNeighbourhoodIsSameObservationPoint → ⊥
noNeighbourhoodPointCollapse ()

record ImageBackCorrelationPolicy : Set where
  constructor image-back-correlation-policy
  field
    allowLocalityPlusImageToPayNeighbourhood : Bool
    requireObservationSpecificCarrierForNativePin : Bool
    preserveObserverConfirmedCoordinateTier : Bool
    requireGISJoinForProjectIntersection : Bool
    prohibitRenderedClusterToNativePinCollapse : Bool

canonicalImageBackCorrelationPolicy : ImageBackCorrelationPolicy
canonicalImageBackCorrelationPolicy = image-back-correlation-policy
  true true true true true
