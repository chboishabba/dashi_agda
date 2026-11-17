module DASHI.Physics.Photovoltaic.GaAs111OpticalDeviceSourceWeldExact where

-- The P1d->P2 gate reuses existing PV, semiconductor and solar-site owners.
-- Source-typed, UNINHABITED physical evidence record. No simulated
-- photoelectron or source string can become a certified measurement.
-- The 111 coherent-film source is NOT a self-assembled finite quantum dot.
-- Source citations, conventions, controls in PVGaAs111... roadmap.
-- Agda Golden checker still OPEN.

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Semiconductor.Device.DriftDiffusionContinuityExact as Continuity
import DASHI.Environment.SolarOpticalSiteFibreCrossPollinationExact as Site
import DASHI.Physics.Photovoltaic.PVPrimaryConversionMaxCutExact as PV
import DASHI.Physics.Photovoltaic.GaAs111PseudomorphicElasticExact as Elastic
import DASHI.Physics.Photovoltaic.GaAs111BirPikusC3vFiniteExact as BP
import DASHI.Physics.Photovoltaic.Atomic369GaAs111TrigonalCharacterExact as Atomic

-- The 6-band gamma values are source-estimated. Their Kane 8-band remapping
-- must explicitly subtract conduction-band coupling in ONE chosen scheme.
-- Each centi-unit identity is source-data arithmetic, NOT a band theorem.
gamma1Centi gamma2Centi gamma3Centi : Nat
gamma1Centi = 698
gamma2Centi = 206
gamma3Centi = 293

hh111InverseMassHundredths hh001InverseMassHundredths : Nat
hh111InverseMassHundredths = 112
hh001InverseMassHundredths = 286

hh111Identity : hh111InverseMassHundredths + 2 * gamma3Centi ≡ gamma1Centi
hh111Identity = refl

hh001Identity : hh001InverseMassHundredths + 2 * gamma2Centi ≡ gamma1Centi
hh001Identity = refl

-- Single-material experiment, not a correspondence inferred from symmetry.
record SameMaterial111OpticalExperiment : Set₁ where
  field
    sameGaAsOrAlloyComposition : String
    sameSubstrateAndGrowthOrientation : String
    sameFilmOrQuantumDotGeometry : String
    strainAndRelaxationMeasurement : String
    temperatureOfEveryFittedParameter : String
    originalSourcesAndErrorBars : String
    sourcePolarizationAndAngleGeometry : String
    measuredPLAndPLE : String
    measuredAbsorptanceSpectrum : String
    measuredEQESpectrum : String
    measuredUnbiasedJVAndPmax : String
    matched001OrUnstrainedControl : String
    excitonExchangeAndFineStructureSource : String
    piezoChargeAndScreeningSource : String
    fullBahderShearAndKStrainSource : String
    independentlyReproducedPVSource : String

-- Exact source witness carriers must be paid independently. Their presence
-- is NOT proven by the finite 269/580 ratio or the closed-form 6-state model.
record SameArtifactPVConversionWeld : Set₁ where
  field
    SiteId Spectrum AngleDist Temperature Shading Soiling Wind Humidity : Set
    siteFibre :
      Site.SolarOpticalSiteFibre SiteId Spectrum AngleDist Temperature
        Shading Soiling Wind Humidity

    sourceOptics : SameMaterial111OpticalExperiment
    sourceFilm : Elastic.Pseudomorphic111SameMaterialAdmission
    continuity : Continuity.CarrierContinuity
    energyLedger : PV.PVPrimaryEnergyWindow

    PhysicalPolarizedAbsorption : Set
    polarizedAbsorption : PhysicalPolarizedAbsorption

    IndependentEQE : Set
    observedEQE : IndependentEQE

    IndependentLoadedJV : Set
    observedLoadedJV : IndependentLoadedJV

    Matched369Prediction : Set
    nontrivial369Prediction : Matched369Prediction

    StandardNetPCE : Set
    independentPCE : StandardNetPCE

-- Explicit NON-promotion: scalar elastic match != measured spectroscopy,
-- finite 8-state energy differences != exciton fine structure,
-- Kane-sum conservation != absorption/extracted charge,
-- same C3v characters != a 369-specific semiconductor advantage.
