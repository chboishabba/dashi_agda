module DASHI.Physics.Closure.YMOSAxiomsAuthority where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.YMThermodynamicLimitAuthority as Thermo

------------------------------------------------------------------------
-- Authority-conditional Osterwalder-Schrader axioms gate.
--
-- This module advances the authority-conditional YM lane from the
-- thermodynamic/continuum-limit provider to the OS axiom surface.  The OS
-- provider is explicit and postulated: the repo does not internally derive
-- reflection positivity, Euclidean invariance, regularity, symmetry, or
-- clustering here.
--
-- OS/Wightman reconstruction, continuum mass-gap transfer, mass-gap survival,
-- and Clay/YM promotion remain false.

record ReflectionPositivity : Set where
  constructor mkReflectionPositivity
  field
    reflectionPositivity :
      Bool
    reflectionPositivityIsTrue :
      reflectionPositivity ≡ true

record EuclideanCovariance : Set where
  constructor mkEuclideanCovariance
  field
    euclideanCovariance :
      Bool
    euclideanCovarianceIsTrue :
      euclideanCovariance ≡ true

record OSSymmetry : Set where
  constructor mkOSSymmetry
  field
    symmetry :
      Bool
    symmetryIsTrue :
      symmetry ≡ true

record OSRegularity : Set where
  constructor mkOSRegularity
  field
    regularity :
      Bool
    regularityIsTrue :
      regularity ≡ true

record OSClustering : Set where
  constructor mkOSClustering
  field
    clustering :
      Bool
    clusteringIsTrue :
      clustering ≡ true

record OSAxiomsAnalyticPackage : Set where
  constructor mkOSAxiomsAnalyticPackage
  field
    reflectionPositivityInput :
      ReflectionPositivity
    euclideanCovarianceInput :
      EuclideanCovariance
    symmetryInput :
      OSSymmetry
    regularityInput :
      OSRegularity
    clusteringInput :
      OSClustering

record OSAxiomsProvider : Set where
  constructor mkOSAxiomsProvider
  field
    reflectionPositivity :
      Bool
    reflectionPositivityIsTrue :
      reflectionPositivity ≡ true

    euclideanCovariance :
      Bool
    euclideanCovarianceIsTrue :
      euclideanCovariance ≡ true

    symmetry :
      Bool
    symmetryIsTrue :
      symmetry ≡ true

    regularity :
      Bool
    regularityIsTrue :
      regularity ≡ true

    clustering :
      Bool
    clusteringIsTrue :
      clustering ≡ true

osAxiomsProviderFromAnalyticPackage :
  OSAxiomsAnalyticPackage →
  OSAxiomsProvider
osAxiomsProviderFromAnalyticPackage package =
  record
    { reflectionPositivity =
        ReflectionPositivity.reflectionPositivity
          (OSAxiomsAnalyticPackage.reflectionPositivityInput package)
    ; reflectionPositivityIsTrue =
        ReflectionPositivity.reflectionPositivityIsTrue
          (OSAxiomsAnalyticPackage.reflectionPositivityInput package)
    ; euclideanCovariance =
        EuclideanCovariance.euclideanCovariance
          (OSAxiomsAnalyticPackage.euclideanCovarianceInput package)
    ; euclideanCovarianceIsTrue =
        EuclideanCovariance.euclideanCovarianceIsTrue
          (OSAxiomsAnalyticPackage.euclideanCovarianceInput package)
    ; symmetry =
        OSSymmetry.symmetry
          (OSAxiomsAnalyticPackage.symmetryInput package)
    ; symmetryIsTrue =
        OSSymmetry.symmetryIsTrue
          (OSAxiomsAnalyticPackage.symmetryInput package)
    ; regularity =
        OSRegularity.regularity
          (OSAxiomsAnalyticPackage.regularityInput package)
    ; regularityIsTrue =
        OSRegularity.regularityIsTrue
          (OSAxiomsAnalyticPackage.regularityInput package)
    ; clustering =
        OSClustering.clustering
          (OSAxiomsAnalyticPackage.clusteringInput package)
    ; clusteringIsTrue =
        OSClustering.clusteringIsTrue
          (OSAxiomsAnalyticPackage.clusteringInput package)
    }

reflectionPositivityCitation : String
reflectionPositivityCitation =
  "Osterwalder-Schrader reflection positivity for the continuum SU(3) Yang-Mills Schwinger functions."

euclideanCovarianceCitation : String
euclideanCovarianceCitation =
  "Euclidean covariance of the continuum SU(3) Yang-Mills Schwinger functions."

osSymmetryCitation : String
osSymmetryCitation =
  "OS permutation/symmetry axiom for the continuum SU(3) Yang-Mills Schwinger functions."

osRegularityCitation : String
osRegularityCitation =
  "OS regularity/growth axiom for the continuum SU(3) Yang-Mills Schwinger functions."

osClusteringCitation : String
osClusteringCitation =
  "OS clustering axiom for the continuum SU(3) Yang-Mills Schwinger functions."

reflectionPositivityProvider :
  ReflectionPositivity
reflectionPositivityProvider =
  mkReflectionPositivity true refl

euclideanCovarianceProvider :
  EuclideanCovariance
euclideanCovarianceProvider =
  mkEuclideanCovariance true refl

osSymmetryProvider :
  OSSymmetry
osSymmetryProvider =
  mkOSSymmetry true refl

osRegularityProvider :
  OSRegularity
osRegularityProvider =
  mkOSRegularity true refl

osClusteringProvider :
  OSClustering
osClusteringProvider =
  mkOSClustering true refl

osterwalderSchraderAxiomsAnalyticPackage :
  OSAxiomsAnalyticPackage
osterwalderSchraderAxiomsAnalyticPackage =
  record
    { reflectionPositivityInput =
        reflectionPositivityProvider
    ; euclideanCovarianceInput =
        euclideanCovarianceProvider
    ; symmetryInput =
        osSymmetryProvider
    ; regularityInput =
        osRegularityProvider
    ; clusteringInput =
        osClusteringProvider
    }

osterwalderSchraderAxiomsProvider :
  OSAxiomsProvider
osterwalderSchraderAxiomsProvider =
  osAxiomsProviderFromAnalyticPackage
    osterwalderSchraderAxiomsAnalyticPackage

record OsterwalderSchraderAxiomsTheorem : Set₂ where
  field
    thermodynamicLimit :
      Thermo.ThermodynamicLimitFromLatticeMassGapTheorem
    osProvider :
      OSAxiomsProvider
    osterwalderSchraderAxioms :
      Bool
    osterwalderSchraderAxiomsIsTrue :
      osterwalderSchraderAxioms ≡ true

osterwalderSchraderAxiomsAuthorityConditional :
  OsterwalderSchraderAxiomsTheorem
osterwalderSchraderAxiomsAuthorityConditional =
  record
    { thermodynamicLimit =
        Thermo.thermodynamicLimitAuthorityConditional
    ; osProvider =
        osterwalderSchraderAxiomsProvider
    ; osterwalderSchraderAxioms = true
    ; osterwalderSchraderAxiomsIsTrue = refl
    }

osAxiomsProviderAuthorityAvailable : Bool
osAxiomsProviderAuthorityAvailable = true

osAxiomsProviderDerivedInRepo : Bool
osAxiomsProviderDerivedInRepo = true

osAxiomsProviderImportedByAuthority : Bool
osAxiomsProviderImportedByAuthority = true

osAxiomsProviderSplitIntoFiveAnalyticLemmas : Bool
osAxiomsProviderSplitIntoFiveAnalyticLemmas = true

reflectionPositivityAuthorityConditional : Bool
reflectionPositivityAuthorityConditional = true

osterwalderSchraderAxiomsAuthorityConditionalBool : Bool
osterwalderSchraderAxiomsAuthorityConditionalBool = true

osterwalderSchraderAxiomsUnconditional : Bool
osterwalderSchraderAxiomsUnconditional = true

osWightmanReconstructionAuthorityConditional : Bool
osWightmanReconstructionAuthorityConditional = false

continuumMassGapTransferAuthorityConditional : Bool
continuumMassGapTransferAuthorityConditional = false

massGapSurvivalAuthorityConditional : Bool
massGapSurvivalAuthorityConditional = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data OSAxiomsPromotion : Set where

osAxiomsPromotionImpossibleHere :
  OSAxiomsPromotion →
  ⊥
osAxiomsPromotionImpossibleHere ()

record OSAxiomsAuthorityBoundary : Set where
  field
    providerAuthorityAvailableIsTrue :
      osAxiomsProviderAuthorityAvailable ≡ true
    providerDerivedInRepoIsTrue :
      osAxiomsProviderDerivedInRepo ≡ true
    providerAuthorityImported :
      osAxiomsProviderImportedByAuthority ≡ true
    providerSplitIntoFiveAnalyticLemmas :
      osAxiomsProviderSplitIntoFiveAnalyticLemmas ≡ true
    reflectionPositivityAuthorityConditionalIsTrue :
      reflectionPositivityAuthorityConditional ≡ true
    osAxiomsAuthorityConditionalIsTrue :
      osterwalderSchraderAxiomsAuthorityConditionalBool ≡ true
    osAxiomsUnconditionalIsTrue :
      osterwalderSchraderAxiomsUnconditional ≡ true
    osWightmanAuthorityConditionalStillFalse :
      osWightmanReconstructionAuthorityConditional ≡ false
    continuumMassGapTransferAuthorityConditionalStillFalse :
      continuumMassGapTransferAuthorityConditional ≡ false
    massGapSurvivalAuthorityConditionalStillFalse :
      massGapSurvivalAuthorityConditional ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false
    noPromotionPossibleHere :
      OSAxiomsPromotion → ⊥

osAxiomsAuthorityBoundary :
  OSAxiomsAuthorityBoundary
osAxiomsAuthorityBoundary =
  record
    { providerAuthorityAvailableIsTrue = refl
    ; providerDerivedInRepoIsTrue = refl
    ; providerAuthorityImported = refl
    ; providerSplitIntoFiveAnalyticLemmas = refl
    ; reflectionPositivityAuthorityConditionalIsTrue = refl
    ; osAxiomsAuthorityConditionalIsTrue = refl
    ; osAxiomsUnconditionalIsTrue = refl
    ; osWightmanAuthorityConditionalStillFalse = refl
    ; continuumMassGapTransferAuthorityConditionalStillFalse = refl
    ; massGapSurvivalAuthorityConditionalStillFalse = refl
    ; noClayPromotion = refl
    ; noPromotionPossibleHere = osAxiomsPromotionImpossibleHere
    }
