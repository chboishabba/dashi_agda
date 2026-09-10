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
  "User-supplied FrogID screenshot maps the capture in the wooded creek landscape west of Springfield; exact coordinates have not yet been extracted."
  "Observer-supplied FrogID capture; taxon remains observer-selected while the visible status is Pending - Submitted and validator comment is absent."
  "Acquire validator outcome and exact coordinates/export before promoting taxon or same-polygon occurrence."

frog948284 : ObserverOccurrenceReceipt
frog948284 = observer-occurrence-receipt
  frogID
  "948284"
  "Johl Brown"
  "2026-09-05 16:37 QLD"
  "Stream or creek"
  "taxon not independently visible in supplied capture-detail screenshot"
  pendingValidation
  "User-supplied FrogID screenshot maps the capture essentially co-located with 948283 in the wooded creek landscape west of Springfield."
  "Observer-supplied FrogID capture; do not transfer the 948283 taxon selection to 948284 without its own result receipt."
  "Acquire the 948284 result/selection and validator outcome; preserve it as a distinct acoustic event."

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

canonicalOccurrenceSnowballPolicy : OccurrenceSnowballPolicy
canonicalOccurrenceSnowballPolicy = occurrence-snowball-policy
  true true true true true true true true
