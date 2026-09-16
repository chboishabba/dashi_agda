module DASHI.Environment.RootNitrogenFluxPrimarySourceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution

------------------------------------------------------------------------
-- PRIMARY ROOT-N FLUX SOURCE
--
-- Trevor Garnett et al.,
-- "Variation for N Uptake System in Maize: Genotypic Response to N Supply",
-- Frontiers in Plant Science 6 (2015), article 936.
-- DOI: 10.3389/fpls.2015.00936.
--
-- The experiment measured short-term (10 min) unidirectional influx of
-- 15N-labelled nitrate and ammonium into maize roots at 200 uM in hydroponic
-- conditions.  The authors interpret the assay as a snapshot of root uptake
-- capacity.  It is not definitionally net field uptake, whole-season crop N,
-- or an arbitrary SPAC root-flux realization.
------------------------------------------------------------------------

data RootNitrogenSpecies : Set where
  nitrate15N
  ammonium15N : RootNitrogenSpecies

record RootNitrogenFluxPrimarySource : Set where
  constructor root-nitrogen-flux-primary-source
  field
    authors : String
    title : String
    venue : String
    year : Nat
    identifier : String
    organism : String
    assayDurationReference : String
    labelledNitrogenConcentrationReference : String
    growthSystemReference : String
    measuredQuantityReference : String
    boundedReading : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner

open RootNitrogenFluxPrimarySource public

garnettMaizeRootFlux2015 : RootNitrogenFluxPrimarySource
garnettMaizeRootFlux2015 = root-nitrogen-flux-primary-source
  "Trevor Garnett; Darren Plett; Vanessa Conn; Simon Conn; Huwaida Rabie; J. Antoni Rafalski; Kanwarpal Dhugga; Mark A. Tester; Brent N. Kaiser"
  "Variation for N Uptake System in Maize: Genotypic Response to N Supply"
  "Frontiers in Plant Science 6:936"
  2015
  "DOI 10.3389/fpls.2015.00936"
  "Zea mays inbred genotypes"
  "10-minute unidirectional influx assay"
  "200 micromolar 15N-labelled nitrate or ammonium"
  "hydroponic plants pre-grown under declared N supplies"
  "15N-derived unidirectional root influx / uptake-capacity snapshot"
  "Direct short-term isotope assay of nitrate and ammonium influx into maize roots under the declared hydroponic assay conditions."
  "Does not establish net field root uptake, whole-season crop uptake, uptake for another species/genotype/N concentration, or an arbitrary SPAC root flux without an exact admission receipt."
  Attribution.primaryPublicationRecord
  Attribution.externalSourceOwner

------------------------------------------------------------------------
-- Non-laundering barriers.
------------------------------------------------------------------------

data UptakeCapacityMeansNetFieldUptakePermission : Set where
data MaizeFluxMeansAllPlantFluxPermission : Set where
data HydroponicFluxMeansSoilFluxPermission : Set where
data RootFluxSourceMeansSPACValidationPermission : Set where
data PrimarySourceOwnsDashiWeldPermission : Set where

uptakeCapacityDoesNotEqualNetFieldUptake :
  UptakeCapacityMeansNetFieldUptakePermission → ⊥
uptakeCapacityDoesNotEqualNetFieldUptake ()

maizeFluxDoesNotGeneraliseToAllPlants :
  MaizeFluxMeansAllPlantFluxPermission → ⊥
maizeFluxDoesNotGeneraliseToAllPlants ()

hydroponicFluxDoesNotEqualSoilFlux :
  HydroponicFluxMeansSoilFluxPermission → ⊥
hydroponicFluxDoesNotEqualSoilFlux ()

rootFluxSourceDoesNotAutomaticallyValidateSPAC :
  RootFluxSourceMeansSPACValidationPermission → ⊥
rootFluxSourceDoesNotAutomaticallyValidateSPAC ()

primarySourceDoesNotOwnDashiWeld :
  PrimarySourceOwnsDashiWeldPermission → ⊥
primarySourceDoesNotOwnDashiWeld ()

record RootNitrogenFluxAttributionBoundary : Set where
  constructor root-nitrogen-flux-attribution-boundary
  field
    externalAssayAndDashiWeldRemainDistinct : Bool
    uptakeCapacityAndNetUptakeRemainDistinct : Bool
    hydroponicAndFieldSoilFluxRemainDistinct : Bool
    genotypeAndSpeciesRemainFirstClass : Bool
    sourceAutomaticallyPaysSPACValidation : Bool

canonicalRootNitrogenFluxAttributionBoundary : RootNitrogenFluxAttributionBoundary
canonicalRootNitrogenFluxAttributionBoundary =
  root-nitrogen-flux-attribution-boundary true true true true false
