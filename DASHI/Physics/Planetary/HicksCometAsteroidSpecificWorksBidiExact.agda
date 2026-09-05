module DASHI.Physics.Planetary.HicksCometAsteroidSpecificWorksBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.InverseProblemIdentifiabilityBidiExact as Inv

------------------------------------------------------------------------
-- Publication-level Hicks science.
-- 1. Hicks & Fink, Spectrophotometry and the Development of Emissions for
--    C/1996 B2 (Comet Hyakutake), Icarus 127 (1997) 307-318,
--    DOI 10.1006/icar.1997.5697.
-- 2. Hicks, Bambery, Lawrence, Kollipara, Near-Nucleus Photometry of Comets
--    Using Archived NEAT Data, Icarus 188 (2007) 457ff.
-- 3. Hicks coauthored physical-model work combining optical/thermal/radar
--    observations of near-Earth asteroids; those multi-channel objects remain
--    separate from the comet-emission pipeline.
------------------------------------------------------------------------

data CometObservable : Set where
  continuumFlux molecularEmission radialEmissionProfile colour : CometObservable


data CometLatent : Set where
  nucleusActivity comaProductionRate speciesAbundance dustContinuum : CometLatent

record CometSpectrophotometryPath : Set where
  constructor comet-spectrophotometry-path
  field
    target : String
    measuredChannels : List CometObservable
    apertureAndGeometryCalibration : String
    emissionSeparationModel : String
    sourceReference : String

open CometSpectrophotometryPath public

hyakutakeSpectrophotometry : CometSpectrophotometryPath
hyakutakeSpectrophotometry = comet-spectrophotometry-path
  "C/1996 B2 (Hyakutake)"
  (continuumFlux ∷ molecularEmission ∷ radialEmissionProfile ∷ [])
  "spectrophotometric calibration plus projected cometocentric geometry"
  "separate dust continuum from gas-emission contributions before physical interpretation"
  "Hicks & Fink 1997, Icarus 127, DOI 10.1006/icar.1997.5697"

record ArchivedPhotometryPath : Set where
  constructor archived-photometry-path
  field
    archive : String
    targetClass : String
    observation : String
    archiveSelectionFunctionRequired : Bool
    archiveSelectionFunctionRequiredIsTrue : archiveSelectionFunctionRequired ≡ true
    sourceReference : String

open ArchivedPhotometryPath public

nearNucleusNEAT : ArchivedPhotometryPath
nearNucleusNEAT = archived-photometry-path
  "Near Earth Asteroid Tracking (NEAT) archive"
  "comets"
  "near-nucleus photometry"
  true refl
  "Hicks et al. 2007, Near-Nucleus Photometry of Comets Using Archived NEAT Data, Icarus 188"

record HicksSpecificWorkBoundary : Set where
  constructor hicks-specific-work-boundary
  field
    broadbandFluxIsGasProductionRateByDefinition : Bool
    broadbandFluxIsGasProductionRateByDefinitionIsFalse :
      broadbandFluxIsGasProductionRateByDefinition ≡ false
    archivedDetectionSampleIsUnbiasedPopulation : Bool
    archivedDetectionSampleIsUnbiasedPopulationIsFalse :
      archivedDetectionSampleIsUnbiasedPopulation ≡ false
    continuumAndEmissionCanBeCollapsedWithoutSeparationModel : Bool
    continuumAndEmissionCanBeCollapsedWithoutSeparationModelIsFalse :
      continuumAndEmissionCanBeCollapsedWithoutSeparationModel ≡ false
    multiEpochPhotometryCanConstrainActivityEvolution : Bool
    multiEpochPhotometryCanConstrainActivityEvolutionIsTrue :
      multiEpochPhotometryCanConstrainActivityEvolution ≡ true

canonicalHicksSpecificWorkBoundary : HicksSpecificWorkBoundary
canonicalHicksSpecificWorkBoundary =
  hicks-specific-work-boundary false refl false refl false refl true refl

hicksCometReverse : Inv.InverseProblemReverseObligation
hicksCometReverse = Inv.inverse-problem-reverse-obligation
  "comet spectrophotometry / near-nucleus photometry"
  "nucleus/coma activity and species-production state"
  "calibrated continuum and molecular-emission fluxes"
  "photometric zero point, aperture, phase/viewing geometry and archive-selection calibration"
  "coma/emission/continuum forward model"
  "dust continuum, gas emission and geometry can trade off in broadband observables"
  "spectral channel / additional epoch / independent gas-production diagnostic"
