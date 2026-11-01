module DASHI.Empirical.DarkDimensionDAOSameKeyExtractionRecipeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Empirical.DarkDimensionDAOParameterManifestBoundaryExact as Manifest
import DASHI.Empirical.DarkDimensionSharedBAOObservableExact as SharedBAO
import DASHI.Empirical.DarkDimensionSharedBAOObservationKeyExact as ObservationKey

------------------------------------------------------------------------
-- DAO / DRMD SAME-KEY EXTRACTION RECIPE
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
    true false false

recipeExecutionStillOpen :
  recipeExecuted daoPinnedExtractionRecipe ≡ false
recipeExecutionStillOpen = refl

sameKeyBAOVectorStillNotDerived :
  sameKeyBAOVectorDerived daoPinnedExtractionRecipe ≡ false
sameKeyBAOVectorStillNotDerived = refl

parameterManifestStillBlocksExecutionClaim :
  Manifest.independentTargetExecutableManifestFrozen
    Manifest.canonicalDAOParameterManifestStatus
  ≡ false
parameterManifestStillBlocksExecutionClaim =
  Manifest.independentTargetManifestStillOpen

------------------------------------------------------------------------
-- Same-key extraction requests.  The coordinate is tied by proof to the
-- observable carried by the observation key, so transverse/radial formulas
-- cannot be silently swapped while remaining well typed.
------------------------------------------------------------------------

data ExtractionCoordinate : Set where
  extractTransverse : ExtractionCoordinate
  extractRadial : ExtractionCoordinate

coordinateObservable : ExtractionCoordinate → SharedBAO.SharedBAOObservable
coordinateObservable extractTransverse = SharedBAO.transverseDMOverRd
coordinateObservable extractRadial = SharedBAO.radialDHOverRd

record SameKeyDAOExtractionRequest : Set where
  constructor sameKeyDAOExtractionRequest
  field
    key : ObservationKey.SharedBAOObservationKey
    coordinate : ExtractionCoordinate
    coordinateMatchesKey :
      coordinateObservable coordinate ≡ ObservationKey.observable key
    recipe : DAOSameKeyExtractionRecipe
    numericalValuePresent : Bool

open SameKeyDAOExtractionRequest public

lrg1TransverseExtractionRequest : SameKeyDAOExtractionRequest
lrg1TransverseExtractionRequest =
  sameKeyDAOExtractionRequest ObservationKey.lrg1TransverseKey extractTransverse refl daoPinnedExtractionRecipe false

lrg1RadialExtractionRequest : SameKeyDAOExtractionRequest
lrg1RadialExtractionRequest =
  sameKeyDAOExtractionRequest ObservationKey.lrg1RadialKey extractRadial refl daoPinnedExtractionRecipe false

lrg2TransverseExtractionRequest : SameKeyDAOExtractionRequest
lrg2TransverseExtractionRequest =
  sameKeyDAOExtractionRequest ObservationKey.lrg2TransverseKey extractTransverse refl daoPinnedExtractionRecipe false

lrg2RadialExtractionRequest : SameKeyDAOExtractionRequest
lrg2RadialExtractionRequest =
  sameKeyDAOExtractionRequest ObservationKey.lrg2RadialKey extractRadial refl daoPinnedExtractionRecipe false

lrg3Elg1TransverseExtractionRequest : SameKeyDAOExtractionRequest
lrg3Elg1TransverseExtractionRequest =
  sameKeyDAOExtractionRequest ObservationKey.lrg3Elg1TransverseKey extractTransverse refl daoPinnedExtractionRecipe false

lrg3Elg1RadialExtractionRequest : SameKeyDAOExtractionRequest
lrg3Elg1RadialExtractionRequest =
  sameKeyDAOExtractionRequest ObservationKey.lrg3Elg1RadialKey extractRadial refl daoPinnedExtractionRecipe false

elg2TransverseExtractionRequest : SameKeyDAOExtractionRequest
elg2TransverseExtractionRequest =
  sameKeyDAOExtractionRequest ObservationKey.elg2TransverseKey extractTransverse refl daoPinnedExtractionRecipe false

elg2RadialExtractionRequest : SameKeyDAOExtractionRequest
elg2RadialExtractionRequest =
  sameKeyDAOExtractionRequest ObservationKey.elg2RadialKey extractRadial refl daoPinnedExtractionRecipe false

qsoTransverseExtractionRequest : SameKeyDAOExtractionRequest
qsoTransverseExtractionRequest =
  sameKeyDAOExtractionRequest ObservationKey.qsoTransverseKey extractTransverse refl daoPinnedExtractionRecipe false

qsoRadialExtractionRequest : SameKeyDAOExtractionRequest
qsoRadialExtractionRequest =
  sameKeyDAOExtractionRequest ObservationKey.qsoRadialKey extractRadial refl daoPinnedExtractionRecipe false

lyaTransverseExtractionRequest : SameKeyDAOExtractionRequest
lyaTransverseExtractionRequest =
  sameKeyDAOExtractionRequest ObservationKey.lyaTransverseKey extractTransverse refl daoPinnedExtractionRecipe false

lyaRadialExtractionRequest : SameKeyDAOExtractionRequest
lyaRadialExtractionRequest =
  sameKeyDAOExtractionRequest ObservationKey.lyaRadialKey extractRadial refl daoPinnedExtractionRecipe false

lrg1TransverseNumericalValueStillOpen :
  numericalValuePresent lrg1TransverseExtractionRequest ≡ false
lrg1TransverseNumericalValueStillOpen = refl

lrg1RadialNumericalValueStillOpen :
  numericalValuePresent lrg1RadialExtractionRequest ≡ false
lrg1RadialNumericalValueStillOpen = refl
