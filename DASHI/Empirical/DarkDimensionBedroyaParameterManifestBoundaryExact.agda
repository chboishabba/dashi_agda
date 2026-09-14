module DASHI.Empirical.DarkDimensionBedroyaParameterManifestBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Empirical.DarkDimensionFadingDMParentLineageExact as ParentLineage

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

-- Bedroya et al. Eq. (11), retained as a source-level normalization identity.
-- This is narrower than a CLASS/Cobaya sampled-parameter map.
effectiveDMNormalizationEquation : String
effectiveDMNormalizationEquation =
  "rho_DM = m0 n0 exp(-cPrime phi_i) a^-3 = rho_DM^0 exp(-cPrime phi_i) a^-3"

onsetPhiInitialValue : String
onsetPhiInitialValue = "phi_i = 0 at the stated fading onset"

paperDMNormalizationIdentityAtOnset : String
paperDMNormalizationIdentityAtOnset = "m0 n0 = rho_DM^0 under phi_i = 0"

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
    effectiveDMNormalizationEquationLocated : Bool
    onsetPhiInitialValueLocated : Bool
    m0n0ToRhoDM0PaperIdentityLocated : Bool
    rhoDM0ToSampledOmegaFDMMappingLocated : Bool
    v0ToSampledDarkEnergyNormalizationLocated : Bool
    completeNormalizationMapLocated : Bool
    supplementPosteriorCoordinatesDisplayed : Bool
    exactStandardBestFitTuplePublished : Bool
    normalizationMapLocated : Bool
    predecessorModelIdentified : Bool
    firstPartyPredecessorImplementationLocatedByCurrentSearch : Bool

open BedroyaParameterManifestStatus public

canonicalBedroyaParameterManifestStatus : BedroyaParameterManifestStatus
canonicalBedroyaParameterManifestStatus =
  bedroyaParameterManifestStatus
    true true true
    true true true
    false false false
    true false false true false

paperDMNormalizationIdentityPaid :
  m0n0ToRhoDM0PaperIdentityLocated canonicalBedroyaParameterManifestStatus ≡ true
paperDMNormalizationIdentityPaid = refl

sampledOmegaFDMMappingStillOpen :
  rhoDM0ToSampledOmegaFDMMappingLocated canonicalBedroyaParameterManifestStatus ≡ false
sampledOmegaFDMMappingStillOpen = refl

v0NormalizationStillOpen :
  v0ToSampledDarkEnergyNormalizationLocated canonicalBedroyaParameterManifestStatus ≡ false
v0NormalizationStillOpen = refl

completeNormalizationStillOpen :
  completeNormalizationMapLocated canonicalBedroyaParameterManifestStatus ≡ false
completeNormalizationStillOpen = refl

data PaperDMIdentityEqualsSampledOmegaMapping : Set where

data OneNormalizationCoordinatePaysCompleteNormalization : Set where

data PosteriorDisplayEqualsExactBestFitTuple : Set where

data StartPrescriptionPaysNormalizationMap : Set where

data CurrentSearchNonlocationProvesNonexistence : Set where

paperDMIdentityDoesNotBecomeSampledOmegaMapping :
  PaperDMIdentityEqualsSampledOmegaMapping → ⊥
paperDMIdentityDoesNotBecomeSampledOmegaMapping ()

partialNormalizationDoesNotCloseCompleteMap :
  OneNormalizationCoordinatePaysCompleteNormalization → ⊥
partialNormalizationDoesNotCloseCompleteMap ()

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

parentLineageStillDoesNotPayNormalizationMap :
  ParentLineage.normalizationInheritanceSameObject
    ParentLineage.canonicalFadingDMParentLineageStatus
  ≡ false
parentLineageStillDoesNotPayNormalizationMap =
  ParentLineage.parentNormalizationInheritanceStillOpen

parentImplementationInheritanceStillOpen :
  ParentLineage.exactImplementationInheritanceDemonstrated
    ParentLineage.canonicalFadingDMParentLineageStatus
  ≡ false
parentImplementationInheritanceStillOpen =
  ParentLineage.parentImplementationInheritanceStillOpen
