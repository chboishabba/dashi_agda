module DASHI.Economics.AIEconomicUsefulWorkSourceAdmissionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Economics.AIEconomicUsefulWorkTimeSeriesExact as TimeSeries
import DASHI.Economics.SourceAttributionPromotionBoundaryExact as Attribution

------------------------------------------------------------------------
-- SOURCE-ADMITTED USEFUL-WORK TIME SERIES
--
-- A citation string is not enough to enter an economic derivative.  Each
-- observation must preserve source ownership, exact metric location and the
-- task/success/cost boundary used by the time-series owner.
------------------------------------------------------------------------

record AttributedTimeSeriesObservation : Set₁ where
  constructor attributedTimeSeriesObservation
  field
    observation : TimeSeries.TimeSeriesObservation
    attribution : Attribution.SourceAttributionReceipt
    metricDefinitionReference : String
    taskDefinitionReference : String
    successCriterionReference : String
    costBoundaryReference : String

open AttributedTimeSeriesObservation public

record TimeSeriesAdmissionReceipt : Set₁ where
  constructor timeSeriesAdmissionReceipt
  field
    attributedObservation : AttributedTimeSeriesObservation
    exactMetricLocationRecovered : Bool
    sourceOwnerPreserved : Bool
    taskDefinitionBound : Bool
    successCriterionBound : Bool
    costBoundaryBoundOrTransported : Bool
    promotionWithinSourceAuthority : Bool

open TimeSeriesAdmissionReceipt public

record ComparableDerivativeAdmission : Set₁ where
  constructor comparableDerivativeAdmission
  field
    before : TimeSeriesAdmissionReceipt
    after : TimeSeriesAdmissionReceipt
    sameEconomicCoordinate : Set
    sameTaskDefinitionOrExplicitTransport : Set
    sameSuccessCriterionOrExplicitTransport : Set
    sameCostBoundaryOrExplicitTransport : Set
    sourceDifferencesDoNotChangeMetricMeaning : Set

open ComparableDerivativeAdmission public

-- Independent observations are an evidentiary property, not a consequence of
-- merely having two URLs, two publications or two corporate entities.
record IndependentTimeSeriesCorroboration : Set₁ where
  constructor independentTimeSeriesCorroboration
  field
    left right : TimeSeriesAdmissionReceipt
    independentProducerReceipt : Attribution.IndependentVerificationReceipt
    sameMetricMeaning : Set

open IndependentTimeSeriesCorroboration public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CitationImpliesTimeSeriesAdmissionPermission : Set where

data SameCoordinateNameImpliesComparableMetricPermission : Set where

data TwoSourcesImpliesIndependentCorroborationPermission : Set where

data VendorMetricImpliesIndependentMarketMetricPermission : Set where

data SourceBackedObservationImpliesEconomicDerivativePermission : Set where

citationDoesNotAutoPromoteToTimeSeriesAdmission :
  CitationImpliesTimeSeriesAdmissionPermission → ⊥
citationDoesNotAutoPromoteToTimeSeriesAdmission ()

sameCoordinateNameDoesNotAutoPromoteToComparableMetric :
  SameCoordinateNameImpliesComparableMetricPermission → ⊥
sameCoordinateNameDoesNotAutoPromoteToComparableMetric ()

twoSourcesDoNotAutoPromoteToIndependentCorroboration :
  TwoSourcesImpliesIndependentCorroborationPermission → ⊥
twoSourcesDoNotAutoPromoteToIndependentCorroboration ()

vendorMetricDoesNotAutoPromoteToIndependentMarketMetric :
  VendorMetricImpliesIndependentMarketMetricPermission → ⊥
vendorMetricDoesNotAutoPromoteToIndependentMarketMetric ()

sourceBackedObservationDoesNotAutoPromoteToEconomicDerivative :
  SourceBackedObservationImpliesEconomicDerivativePermission → ⊥
sourceBackedObservationDoesNotAutoPromoteToEconomicDerivative ()

sourceCarrierDoesNotManufactureAuthorship :
  Attribution.AccessCarrierImpliesAuthorshipPermission → ⊥
sourceCarrierDoesNotManufactureAuthorship =
  Attribution.accessCarrierDoesNotAutoPromoteToAuthorship

sameContentDoesNotManufactureIndependentProducer :
  Attribution.SameContentImpliesIndependentProducerPermission → ⊥
sameContentDoesNotManufactureIndependentProducer =
  Attribution.sameContentDoesNotAutoPromoteToIndependentProducer
