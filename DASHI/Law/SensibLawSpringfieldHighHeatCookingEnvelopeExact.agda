module DASHI.Law.SensibLawSpringfieldHighHeatCookingEnvelopeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- HIGH-HEAT COOKING CAPABILITY / DWELLING ENVELOPE AUDIT
--
-- Clarification owner: recurrent alarm observations are NOT treated as evidence
-- that gas caused an alarm.  They are only a locator for a compatibility audit
-- between the installed high-heat cooking capability (including a gas wok
-- burner), ventilation / rangehood / make-up air, alarm placement/type and the
-- broader dwelling envelope.
------------------------------------------------------------------------

data CookingEnvelopeFeature : Set where
  installedGasWokBurner : CookingEnvelopeFeature
  mixedFuelCooktop : CookingEnvelopeFeature
  recurrentAlarmSound : CookingEnvelopeFeature
  compactRowhouseKitchenEnvelope : CookingEnvelopeFeature
  ventilationCapacityUnknown : CookingEnvelopeFeature
  alarmPlacementAndTypeUnknown : CookingEnvelopeFeature

data ObservationStatus : Set where
  operatorReported : ObservationStatus
  sourceDocumentPaid : ObservationStatus
  instrumentVerified : ObservationStatus
  unresolved : ObservationStatus

record CookingEnvelopeObservation : Set where
  constructor cooking-envelope-observation
  field
    feature : CookingEnvelopeFeature
    statement : String
    status : ObservationStatus
    exactAddressPublished : Bool
    exactAddressPublishedIsFalse : exactAddressPublished ≡ false

open CookingEnvelopeObservation public

gasWokBurnerObservation : CookingEnvelopeObservation
gasWokBurnerObservation = cooking-envelope-observation
  installedGasWokBurner
  "De-identified investigator observation: the dwelling has a gas wok burner as part of a mixed-fuel cooking arrangement. This is a high-heat-capability observation, not evidence about why the appliance was selected."
  operatorReported
  false refl

recurrentAlarmAsCompatibilityLocator : CookingEnvelopeObservation
recurrentAlarmAsCompatibilityLocator = cooking-envelope-observation
  recurrentAlarmSound
  "De-identified investigator observation: alarms are heard recurrently across the complex. No claim is made that gas causes the alarms. The observation selects a producer search about whether the dwelling envelope, rangehood/ventilation and alarm architecture are suitable for the installed high-heat cooking capability."
  operatorReported
  false refl

------------------------------------------------------------------------
-- Residuals: pay compatibility with exact project/appliance/building records.
------------------------------------------------------------------------

data CompatibilityHypothesis : Set where
  highHeatCapabilityOutrunsDwellingEnvelope : CompatibilityHypothesis
  ventilationMayBeUnderspecifiedForInstalledCapability : CompatibilityHypothesis
  alarmArchitectureMayBeSensitiveToOrdinaryHighHeatCooking : CompatibilityHypothesis

data RequiredProducer : Set where
  originalCooktopAndWokBurnerSpecification : RequiredProducer
  rangehoodSpecificationAndDuctRoute : RequiredProducer
  kitchenVentilationAndMakeupAirDesign : RequiredProducer
  smokeAlarmTypeLocationAndCommissioningRecord : RequiredProducer
  projectMechanicalHydraulicAndArchitecturalPlans : RequiredProducer
  ordinaryCookingEventObservationOrMeasurement : RequiredProducer

record CompatibilityResidual : Set where
  constructor compatibility-residual
  field
    hypothesis : CompatibilityHypothesis
    producer : RequiredProducer
    paid : Bool
    boundary : String

open CompatibilityResidual public

highHeatCapabilityEnvelopeResidual : CompatibilityResidual
highHeatCapabilityEnvelopeResidual = compatibility-residual
  highHeatCapabilityOutrunsDwellingEnvelope
  projectMechanicalHydraulicAndArchitecturalPlans
  false
  "A gas wok burner indicates installed high-heat cooking capability, but whether the dwelling was actually designed to support that capability requires the exact architectural/mechanical/appliance design and commissioning records."

rangehoodAndMakeupAirResidual : CompatibilityResidual
rangehoodAndMakeupAirResidual = compatibility-residual
  ventilationMayBeUnderspecifiedForInstalledCapability
  kitchenVentilationAndMakeupAirDesign
  false
  "Repeated alarm observations and a high-heat burner select a ventilation-capacity inquiry. They do not establish inadequate ventilation without rangehood airflow, ducting, make-up-air and room-envelope evidence."

alarmCauseRemainsUnpaid : CompatibilityResidual
alarmCauseRemainsUnpaid = compatibility-residual
  alarmArchitectureMayBeSensitiveToOrdinaryHighHeatCooking
  smokeAlarmTypeLocationAndCommissioningRecord
  false
  "The cause of any particular alarm remains unpaid. Acquire alarm type/location, commissioning records and event-level evidence before attributing an alarm to cooking, gas, smoke, heat or any other cause."

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data AlarmFrequencyProvesGasCause : Set where
data WokBurnerProvesAdequateVentilation : Set where
data AdvertisedHighHeatCapabilityProvesDwellingSuitability : Set where
data AlarmFrequencyProvesCodeBreach : Set where

alarmFrequencyDoesNotProveGasCause : AlarmFrequencyProvesGasCause → ⊥
alarmFrequencyDoesNotProveGasCause ()

wokBurnerDoesNotProveAdequateVentilation : WokBurnerProvesAdequateVentilation → ⊥
wokBurnerDoesNotProveAdequateVentilation ()

advertisedHighHeatCapabilityDoesNotProveDwellingSuitability : AdvertisedHighHeatCapabilityProvesDwellingSuitability → ⊥
advertisedHighHeatCapabilityDoesNotProveDwellingSuitability ()

alarmFrequencyDoesNotProveCodeBreach : AlarmFrequencyProvesCodeBreach → ⊥
alarmFrequencyDoesNotProveCodeBreach ()

------------------------------------------------------------------------
-- Pareto route.
------------------------------------------------------------------------

record HighHeatCookingPareto : Set where
  constructor high-heat-cooking-pareto
  field
    exactApplianceSpecFirst : Bool
    exactRangehoodAndDuctingSecond : Bool
    alarmTypeAndPlacementThird : Bool
    projectEnvelopePlansFourth : Bool
    eventLevelMeasurementBeforeCause : Bool
    compatibilityBeforeIntent : Bool
    alarmObservationMaySelectProducer : Bool
    alarmObservationMayPayGasCause : Bool

canonicalHighHeatCookingPareto : HighHeatCookingPareto
canonicalHighHeatCookingPareto = high-heat-cooking-pareto
  true true true true true true true false
