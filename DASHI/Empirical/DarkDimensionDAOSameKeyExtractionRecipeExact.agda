module DASHI.Empirical.DarkDimensionDAOSameKeyExtractionRecipeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Empirical.DarkDimensionSharedBAOObservationKeyExact as ObservationKey

------------------------------------------------------------------------
-- DAO / DRMD SAME-KEY EXTRACTION RECIPE
--
-- This owner records a reproducible recipe against the pinned public
-- NEDE-Cosmo/DRMD-CLASS source tree.  It is deliberately a recipe receipt,
-- not an execution receipt and not a numerical prediction.
--
-- Source surfaces inspected at revision
--   aa2b61a0f1cf246672cdbd4634a4797d4cc654f9
-- include:
--   input/DRMD.ini         -- model input parameters
--   python/classy.pyx     -- angular_distance, Hubble, rs_drag API
--   scripts/distances.py  -- repository example of background-distance access
--
-- For each DESI observation key z:
--   D_M(z)/r_d = (1+z) * angular_distance(z) / rs_drag
--   D_H(z)/r_d = (1/Hubble(z)) / rs_drag
--
-- Important WrongType boundary:
--   rs_drag   = baryon-drag sound horizon used by the DESI BAO denominator;
--   rs_d_drmd = model-specific dark-radiation/matter sound horizon.
-- The public DRMD repository exposes both, but they are not interchangeable.
------------------------------------------------------------------------

transverseDistanceFormula : String
transverseDistanceFormula =
  "D_M(z)/r_d = (1+z) * angular_distance(z) / rs_drag"

radialDistanceFormula : String
radialDistanceFormula =
  "D_H(z)/r_d = (1/Hubble(z)) / rs_drag"

data DarkSoundHorizonSubstitutesForBAODragHorizon : Set where

darkSoundHorizonDoesNotSubstituteForBAODragHorizon :
  DarkSoundHorizonSubstitutesForBAODragHorizon → ⊥
darkSoundHorizonDoesNotSubstituteForBAODragHorizon ()

darkSoundHorizonAPI : String
darkSoundHorizonAPI = "rs_d_drmd"

record DAOSameKeyExtractionRecipe : Set where
  constructor daoSameKeyExtractionRecipe
  field
    repository : String
    revision : String
    modelInputPath : String
    pythonInterfacePath : String
    distanceExamplePath : String
    angularDistanceAPI : String
    hubbleAPI : String
    dragSoundHorizonAPI : String
    modelSpecificDarkSoundHorizonAPI : String
    transverseFormula : String
    radialFormula : String
    recipeSourcePinned : Bool
    recipeExecuted : Bool
    sameKeyBAOVectorDerived : Bool

open DAOSameKeyExtractionRecipe public

daoPinnedExtractionRecipe : DAOSameKeyExtractionRecipe
daoPinnedExtractionRecipe =
  daoSameKeyExtractionRecipe
    "NEDE-Cosmo/DRMD-CLASS"
    "aa2b61a0f1cf246672cdbd4634a4797d4cc654f9"
    "input/DRMD.ini"
    "python/classy.pyx"
    "scripts/distances.py"
    "angular_distance"
    "Hubble"
    "rs_drag"
    darkSoundHorizonAPI
    transverseDistanceFormula
    radialDistanceFormula
    true
    false
    false

recipeExecutionStillOpen :
  recipeExecuted daoPinnedExtractionRecipe ≡ false
recipeExecutionStillOpen = refl

sameKeyBAOVectorStillNotDerived :
  sameKeyBAOVectorDerived daoPinnedExtractionRecipe ≡ false
sameKeyBAOVectorStillNotDerived = refl

------------------------------------------------------------------------
-- Same-key extraction requests.  These retain the exact observation identity
-- while naming which recipe coordinate must be evaluated.
------------------------------------------------------------------------

data ExtractionCoordinate : Set where
  extractTransverse : ExtractionCoordinate
  extractRadial : ExtractionCoordinate

record SameKeyDAOExtractionRequest : Set where
  constructor sameKeyDAOExtractionRequest
  field
    key : ObservationKey.SharedBAOObservationKey
    coordinate : ExtractionCoordinate
    recipe : DAOSameKeyExtractionRecipe
    numericalValuePresent : Bool

open SameKeyDAOExtractionRequest public

lrg1TransverseExtractionRequest : SameKeyDAOExtractionRequest
lrg1TransverseExtractionRequest =
  sameKeyDAOExtractionRequest
    ObservationKey.lrg1TransverseKey
    extractTransverse
    daoPinnedExtractionRecipe
    false

lrg1RadialExtractionRequest : SameKeyDAOExtractionRequest
lrg1RadialExtractionRequest =
  sameKeyDAOExtractionRequest
    ObservationKey.lrg1RadialKey
    extractRadial
    daoPinnedExtractionRecipe
    false

lrg1TransverseNumericalValueStillOpen :
  numericalValuePresent lrg1TransverseExtractionRequest ≡ false
lrg1TransverseNumericalValueStillOpen = refl

lrg1RadialNumericalValueStillOpen :
  numericalValuePresent lrg1RadialExtractionRequest ≡ false
lrg1RadialNumericalValueStillOpen = refl
