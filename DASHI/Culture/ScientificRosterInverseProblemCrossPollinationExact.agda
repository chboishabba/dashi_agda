module DASHI.Culture.ScientificRosterInverseProblemCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.InverseProblemIdentifiabilityBidiExact as Inv

------------------------------------------------------------------------
-- CROSS-ROSTER INVERSE-PROBLEM SOCKETS
--
-- These are theorem-shape correspondences only.  They preserve distinct
-- forward models, latent carriers and calibration regimes.
------------------------------------------------------------------------

data RosterScienceLane : Set where
  loureiroHermite
  leblancSensors
  maiwaldActionSpectrum
  rezaAlloyPerformance
  grillmairStreams
  hicksSmallBodies
  chavezRadiography
  thomasSignalling
  : RosterScienceLane

record LaneInverseProfile : Set where
  constructor lane-inverse-profile
  field
    lane : RosterScienceLane
    latentState : String
    firstObservation : String
    requiredCalibration : String
    forwardModel : String
    degeneracy : String
    usefulSecondChannel : String
    sourceOrRepoReference : String

open LaneInverseProfile public

loureiroProfile : LaneInverseProfile
loureiroProfile = lane-inverse-profile
  loureiroHermite
  "electron parallel-velocity distribution / kinetic state"
  "finite Hermite coefficient vector"
  "Hermite normalization, truncation and closure convention"
  "KREHM/KRMHD velocity-space moment projection"
  "distinct unresolved tails can share retained low-m coefficients"
  "higher Hermite order / alternative kinetic diagnostic"
  "Loureiro Viriato BIDI owner"

leblancProfile : LaneInverseProfile
leblancProfile = lane-inverse-profile
  leblancSensors
  "reactor / plant condition"
  "finite sensor telemetry"
  "sensor transfer function, radiation/temperature drift and qualification"
  "instrumentation-and-controls state estimator"
  "different faults may produce similar sensor patterns"
  "independent sensor modality / redundancy"
  "LeBlanc FSP I&C BIDI owner"

maiwaldProfile : LaneInverseProfile
maiwaldProfile = lane-inverse-profile
  maiwaldActionSpectrum
  "molecular identity / isomeric structure"
  "frequency-dependent photodissociation action yield"
  "laser frequency/intensity and trap-response calibration"
  "messenger-tagged action-spectroscopy response model"
  "different species can overlap in partial spectral windows"
  "orthogonal spectral region / mass or fragmentation channel"
  "Maiwald action-spectroscopy BIDI owner"

rezaProfile : LaneInverseProfile
rezaProfile = lane-inverse-profile
  rezaAlloyPerformance
  "microstructure plus composition plus processing state"
  "bulk composition / mechanical or burn-resistance test"
  "composition assay and test-environment calibration"
  "composition-processing-microstructure-property relation"
  "same nominal composition can realize different microstructures/performance"
  "microstructure microscopy / independent mechanical or oxidation test"
  "Reza burn-resistant alloy BIDI owner"

grillmairProfile : LaneInverseProfile
grillmairProfile = lane-inverse-profile
  grillmairStreams
  "orbit/progenitor state in a Galactic potential"
  "projected stellar-stream track"
  "distance scale, survey selection and astrometric calibration"
  "orbit/stream-generation model in Galactic potential"
  "different orbit/potential combinations can project similarly"
  "radial velocity / proper motion / distance gradient"
  "Grillmair stellar-stream BIDI owner"

hicksProfile : LaneInverseProfile
hicksProfile = lane-inverse-profile
  hicksSmallBodies
  "small-body shape/rotation/albedo/composition/thermal state"
  "lightcurve or spectrum"
  "photometric/spectral geometry and instrument calibration"
  "scattering/thermal/shape forward model"
  "shape-pole-albedo-composition degeneracies"
  "thermal IR / radar / spectroscopy / multi-epoch geometry"
  "Hicks small-body BIDI owner"

chavezProfile : LaneInverseProfile
chavezProfile = lane-inverse-profile
  chavezRadiography
  "time-resolved material density/state"
  "X-ray transmission radiograph"
  "source spectrum, detector response and geometry calibration"
  "radiographic transport/attenuation forward model"
  "source intensity, thickness and opacity can trade off"
  "second view / energy / time frame / independent diagnostic"
  "Anthony Chavez Scorpius BIDI owner"

thomasProfile : LaneInverseProfile
thomasProfile = lane-inverse-profile
  thomasSignalling
  "pathway state / direct compound target / autophagy mechanism"
  "nuclear-translocation or abundance/localisation readout"
  "assay dynamic range, controls and perturbation calibration"
  "cellular signalling/trafficking response model"
  "multiple targets/pathways can produce similar phenotypic readouts"
  "orthogonal biochemical, genetic or binding assay"
  "Jason Thomas signalling BIDI owner"

------------------------------------------------------------------------
-- Reverse acquisition compiler.
------------------------------------------------------------------------

profileToReverseObligation : LaneInverseProfile → Inv.InverseProblemReverseObligation
profileToReverseObligation p =
  Inv.inverse-problem-reverse-obligation
    (sourceOrRepoReference p)
    (latentState p)
    (firstObservation p)
    (requiredCalibration p)
    (forwardModel p)
    (degeneracy p)
    (usefulSecondChannel p)

------------------------------------------------------------------------
-- Explicit cross-domain firewall.
------------------------------------------------------------------------

record CrossRosterInverseBoundary : Set where
  constructor cross-roster-inverse-boundary
  field
    sharedInverseShapeImpliesSamePhysics : Bool
    sharedInverseShapeImpliesSamePhysicsIsFalse : sharedInverseShapeImpliesSamePhysics ≡ false
    sameNeedForCalibrationImpliesSameInstrument : Bool
    sameNeedForCalibrationImpliesSameInstrumentIsFalse : sameNeedForCalibrationImpliesSameInstrument ≡ false
    secondChannelAlwaysGuaranteesIdentifiability : Bool
    secondChannelAlwaysGuaranteesIdentifiabilityIsFalse : secondChannelAlwaysGuaranteesIdentifiability ≡ false
    sharedBidiShapeSupportsGenericProofSearch : Bool
    sharedBidiShapeSupportsGenericProofSearchIsTrue : sharedBidiShapeSupportsGenericProofSearch ≡ true

canonicalCrossRosterInverseBoundary : CrossRosterInverseBoundary
canonicalCrossRosterInverseBoundary = cross-roster-inverse-boundary
  false refl false refl false refl true refl
