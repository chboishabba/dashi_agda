module DASHI.Empirical.DarkDimensionBedroyaParameterManifestBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.EmpiricalSourceDiligenceAdmissionExact as Diligence
import DASHI.Physics.Closure.DarkDimensionStringPromotionBoundaryExact as DarkDimension
import DASHI.Empirical.DarkDimensionFadingDMParentLineageExact as ParentLineage

bedroyaNormalizationSource : Source.AttributedSource
bedroyaNormalizationSource = DarkDimension.bedroyaObiedVafaWu2026

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

effectiveDMNormalizationEquation : String
effectiveDMNormalizationEquation =
  "rho_DM = m0 n0 exp(-cPrime phi_i) a^-3 = rho_DM^0 exp(-cPrime phi_i) a^-3"

onsetPhiInitialValue : String
onsetPhiInitialValue = "phi_i = 0 at the stated fading onset"

paperDMNormalizationIdentityAtOnset : String
paperDMNormalizationIdentityAtOnset = "m0 n0 = rho_DM^0 under phi_i = 0"

effectiveDMReferenceConvention : String
effectiveDMReferenceConvention = "initial DM density reference, not current-DM subtraction"

bedroyaEq11NormalizationDiligence : Diligence.SourceDiligence
bedroyaEq11NormalizationDiligence =
  Diligence.source-diligence
    "Bedroya-Obied-Vafa-Wu Eq. (11) dark-matter normalization identity"
    bedroyaNormalizationSource
    Diligence.primaryProposition
    true
    refl
    "arXiv:2507.03090v3 primary HTML/manuscript inspected at Section IV equations (10)-(17)"
    Diligence.primaryLocated
    "Eq. (11) defines the effective pressureless DM density from the initial DM density; the onset field value phi_i is the field value at onset, with the stated fading onset set at phi=0"
    "arXiv:2507.03090v3 dated 29 May 2026; accepted Physical Review D source DOI 10.1103/1rsq-cv2m"
    "same 2026 Bedroya-Obied-Vafa-Wu fading-dark-sector model object"
    "bounded to the paper's local exponential FDS realization and its stated onset convention"
    "covers the paper-level m0*n0 / rho_DM^0 identity only; does not cover the CLASS/Cobaya sampled-density parameter map or V0 normalization"
    "supplement/posterior surfaces were checked separately; no machine-readable same-fit standard-parameter manifest is admitted"
    "rho_DM^0 is retained as the paper-defined effective initial DM density coordinate; it is not silently identified with a sampled Omega_FDM h^2 coordinate or a current-density subtraction convention"
    "pays only the source-level Eq. (11) normalization coordinate and leaves the complete executable normalization map open"

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
    effectiveDMReferenceUsesInitialDensity : Bool
    currentDensitySubtractionConventionUsed : Bool
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
    true false
    false false false
    true false false true false

paperDMNormalizationIdentityPaid :
  m0n0ToRhoDM0PaperIdentityLocated canonicalBedroyaParameterManifestStatus ≡ true
paperDMNormalizationIdentityPaid = refl

initialDensityConventionPaid :
  effectiveDMReferenceUsesInitialDensity canonicalBedroyaParameterManifestStatus ≡ true
initialDensityConventionPaid = refl

currentDensityConventionNotUsed :
  currentDensitySubtractionConventionUsed canonicalBedroyaParameterManifestStatus ≡ false
currentDensityConventionNotUsed = refl

sampledOmegaFDMMappingStillOpen :
  rhoDM0ToSampledOmegaFDMMappingLocated canonicalBedroyaParameterManifestStatus ≡ false
sampledOmegaFDMMappingStillOpen = refl

v0NormalizationStillOpen :
  v0ToSampledDarkEnergyNormalizationLocated canonicalBedroyaParameterManifestStatus ≡ false
v0NormalizationStillOpen = refl

completeNormalizationStillOpen :
  completeNormalizationMapLocated canonicalBedroyaParameterManifestStatus ≡ false
completeNormalizationStillOpen = refl

data InitialDMReferenceEqualsCurrentDMReference : Set where

data PaperDMIdentityEqualsSampledOmegaMapping : Set where

data OneNormalizationCoordinatePaysCompleteNormalization : Set where

data PosteriorDisplayEqualsExactBestFitTuple : Set where

data StartPrescriptionPaysNormalizationMap : Set where

data CurrentSearchNonlocationProvesNonexistence : Set where

initialDMReferenceDoesNotBecomeCurrentDMReference :
  InitialDMReferenceEqualsCurrentDMReference → ⊥
initialDMReferenceDoesNotBecomeCurrentDMReference ()

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
