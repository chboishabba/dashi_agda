{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974MaterialDependentThermalFalsifierExact where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Propulsion.Rocketdyne1974TwoMaterialDiscriminatorExact as D

------------------------------------------------------------------------
-- TEMPERATURE-ONLY MODEL FALSIFIER
--
-- The source reports about 2300 F equilibrium nozzle temperature for both the
-- damaged Haynes-25 test and the later WC103-columbium rerun, but the outcomes
-- differ. Therefore no deterministic predictor whose ONLY input is reported
-- equilibrium nozzle temperature can fit both observations.
--
-- This proves insufficiency of the temperature-only observation map. It does
-- NOT prove material identity is the unique cause: geometry, coating, stress,
-- boundary conditions and other documented hardware differences remain live.
------------------------------------------------------------------------

sameReportedEquilibriumTemperature :
  D.HistoricalRun.equilibriumNozzleTemperatureF D.haynesDamageObserved ≡
  D.HistoricalRun.equilibriumNozzleTemperatureF D.wc103FollowupSurvived
sameReportedEquilibriumTemperature = refl

wc103LongerExposureSurvived : Bool
wc103LongerExposureSurvived = true

TemperatureOnlyModel : Set
TemperatureOnlyModel = Nat → D.ObservedOutcome

materialBlindTemperatureOnlyModelRefuted :
  (m : TemperatureOnlyModel) →
  m 2300 ≡ D.damaged →
  m 2300 ≡ D.survivedObservedRun →
  ⊥
materialBlindTemperatureOnlyModelRefuted m refl ()

------------------------------------------------------------------------
-- Stronger duration monotonicity cut.
--
-- If a material-blind model uses only temperature and exposure duration, and
-- once damaged at fixed temperature must remain damaged at longer exposure,
-- then fitting the 10 s damaged Haynes observation forces damage at 45 s. The
-- observed WC103 45 s survival therefore refutes that model family as well.
------------------------------------------------------------------------

TemperatureDurationModel : Set
TemperatureDurationModel = Nat → Nat → D.ObservedOutcome

record DamagePersistsWithLongerExposure (m : TemperatureDurationModel) : Set where
  constructor damage-persists
  field
    tenToFortyFiveAt2300 :
      m 2300 10 ≡ D.damaged →
      m 2300 45 ≡ D.damaged

materialBlindMonotoneDurationModelRefuted :
  (m : TemperatureDurationModel) →
  DamagePersistsWithLongerExposure m →
  m 2300 10 ≡ D.damaged →
  m 2300 45 ≡ D.survivedObservedRun →
  ⊥
materialBlindMonotoneDurationModelRefuted m persistence h w
  with DamagePersistsWithLongerExposure.tenToFortyFiveAt2300 persistence h
... | refl with w
... | ()

record MaterialDependenceBoundary : Set where
  constructor material-dependence-boundary
  field
    temperatureOnlyObservationSufficient : Bool
    temperatureAndMonotoneDurationSufficient : Bool
    atLeastOneNonTemperatureCoordinateRequired : Bool
    materialIdentityIsDocumentedChangedCoordinate : Bool
    materialIdentityAloneProvenCausal : Bool
    exactSingleVariableExperiment : Bool
    sourceReference : String

canonicalMaterialDependenceBoundary : MaterialDependenceBoundary
canonicalMaterialDependenceBoundary =
  material-dependence-boundary
    false false true true false false
    "NASA-CR-140308 R-9557 p.155 / Fig.78; R-9557-1 pp.26-28"

-- Required for any model that wants to claim a MATERIAL effect specifically:
-- material identity must be an explicit model coordinate rather than erased.
materialIdentityIsNecessaryDiscriminator : Bool
materialIdentityIsNecessaryDiscriminator =
  MaterialDependenceBoundary.materialIdentityIsDocumentedChangedCoordinate
    canonicalMaterialDependenceBoundary
