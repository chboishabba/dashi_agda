module DASHI.Empirical.DarkDimensionBedroyaParameterManifestBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

simulationStartRedshift : String
simulationStartRedshift = "1e14"

fadingOnsetPhi : String
fadingOnsetPhi = "phi = 0"

initialMassScaleDefinition : String
initialMassScaleDefinition = "m0 = initial dark-matter mass scale"

initialNumberDensityDefinition : String
initialNumberDensityDefinition = "n0 = initial dark-matter number-density scale"

initialPotentialScaleDefinition : String
initialPotentialScaleDefinition = "V0 = scalar-potential energy scale"

supplementH0Coordinate : String
supplementH0Coordinate = "H0"

supplementOmegaBCoordinate : String
supplementOmegaBCoordinate = "Omega_b h^2"

supplementOmegaFDMCoordinate : String
supplementOmegaFDMCoordinate = "Omega_FDM h^2"

supplementSigma8Coordinate : String
supplementSigma8Coordinate = "sigma8"

supplementRDragCoordinate : String
supplementRDragCoordinate = "r_drag"

predecessorArXiv : String
predecessorArXiv = "1906.08261"

record BedroyaParameterManifestStatus : Set where
  constructor bedroyaParameterManifestStatus
  field
    simulationStartRedshiftLocated : Bool
    fadingOnsetPhiLocated : Bool
    initialScaleDefinitionsLocated : Bool
    supplementPosteriorCoordinatesDisplayed : Bool
    exactStandardBestFitTuplePublished : Bool
    normalizationMapLocated : Bool
    predecessorModelIdentified : Bool
    firstPartyPredecessorImplementationLocatedByCurrentSearch : Bool

open BedroyaParameterManifestStatus public

canonicalBedroyaParameterManifestStatus : BedroyaParameterManifestStatus
canonicalBedroyaParameterManifestStatus =
  bedroyaParameterManifestStatus true true true true false false true false

data PosteriorDisplayEqualsExactBestFitTuple : Set where

data StartPrescriptionPaysNormalizationMap : Set where

data CurrentSearchNonlocationProvesNonexistence : Set where

posteriorDisplayDoesNotEqualExactBestFitTuple :
  PosteriorDisplayEqualsExactBestFitTuple → ⊥
posteriorDisplayDoesNotEqualExactBestFitTuple ()

startPrescriptionDoesNotPayNormalizationMap :
  StartPrescriptionPaysNormalizationMap → ⊥
startPrescriptionDoesNotPayNormalizationMap ()

unlocatedImplementationDoesNotProveNonexistence :
  CurrentSearchNonlocationProvesNonexistence → ⊥
unlocatedImplementationDoesNotProveNonexistence ()

exactStandardTupleStillOpen :
  exactStandardBestFitTuplePublished canonicalBedroyaParameterManifestStatus ≡ false
exactStandardTupleStillOpen = refl

normalizationMapStillOpen :
  normalizationMapLocated canonicalBedroyaParameterManifestStatus ≡ false
normalizationMapStillOpen = refl

predecessorImplementationStillUnlocatedByCurrentSearch :
  firstPartyPredecessorImplementationLocatedByCurrentSearch canonicalBedroyaParameterManifestStatus
  ≡ false
predecessorImplementationStillUnlocatedByCurrentSearch = refl
