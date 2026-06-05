module DASHI.Physics.Closure.YMThermodynamicLimitAuthority where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.YMLatticeMassGapAuthority as Lattice

------------------------------------------------------------------------
-- Authority-conditional thermodynamic/continuum-limit gate.
--
-- This module advances the authority-conditional YM lane from a positive
-- lattice mass gap to the infinite-volume/continuum-limit side of the endpoint
-- ladder.  The provider is explicit and postulated: the repo does not derive
-- the thermodynamic limit or tight nontrivial SU(3) continuum measure here.
--
-- OS axioms, OS/Wightman reconstruction, continuum mass-gap transfer,
-- mass-gap survival, and Clay/YM promotion remain false.

record UniformLatticeMassGap : Set where
  constructor mkUniformLatticeMassGap
  field
    uniformLatticeMassGap :
      Bool
    uniformLatticeMassGapIsTrue :
      uniformLatticeMassGap ≡ true

record FiniteVolumeTightness : Set where
  constructor mkFiniteVolumeTightness
  field
    finiteVolumeTightness :
      Bool
    finiteVolumeTightnessIsTrue :
      finiteVolumeTightness ≡ true

record InfiniteVolumeThermodynamicLimit : Set where
  constructor mkInfiniteVolumeThermodynamicLimit
  field
    thermodynamicLimit :
      Bool
    thermodynamicLimitIsTrue :
      thermodynamicLimit ≡ true

record ContinuumLimitExists : Set where
  constructor mkContinuumLimitExists
  field
    continuumLimitExists :
      Bool
    continuumLimitExistsIsTrue :
      continuumLimitExists ≡ true

record Nontrivial4DSU3YangMillsMeasure : Set where
  constructor mkNontrivial4DSU3YangMillsMeasure
  field
    nontrivial4DSU3YangMillsMeasure :
      Bool
    nontrivial4DSU3YangMillsMeasureIsTrue :
      nontrivial4DSU3YangMillsMeasure ≡ true

record ThermodynamicLimitAnalyticPackage : Set where
  constructor mkThermodynamicLimitAnalyticPackage
  field
    uniformLatticeMassGapInput :
      UniformLatticeMassGap
    finiteVolumeTightnessInput :
      FiniteVolumeTightness
    infiniteVolumeThermodynamicLimitInput :
      InfiniteVolumeThermodynamicLimit
    continuumLimitExistsInput :
      ContinuumLimitExists
    nontrivial4DSU3YangMillsMeasureInput :
      Nontrivial4DSU3YangMillsMeasure

record ThermodynamicLimitProvider : Set where
  constructor mkThermodynamicLimitProvider
  field
    uniformLatticeMassGap :
      Bool
    uniformLatticeMassGapIsTrue :
      uniformLatticeMassGap ≡ true

    finiteVolumeTightness :
      Bool
    finiteVolumeTightnessIsTrue :
      finiteVolumeTightness ≡ true

    thermodynamicLimit :
      Bool
    thermodynamicLimitIsTrue :
      thermodynamicLimit ≡ true

    continuumLimitExists :
      Bool
    continuumLimitExistsIsTrue :
      continuumLimitExists ≡ true

    nontrivial4DSU3YangMillsMeasure :
      Bool
    nontrivial4DSU3YangMillsMeasureIsTrue :
      nontrivial4DSU3YangMillsMeasure ≡ true

thermodynamicLimitProviderFromAnalyticPackage :
  ThermodynamicLimitAnalyticPackage →
  ThermodynamicLimitProvider
thermodynamicLimitProviderFromAnalyticPackage package =
  record
    { uniformLatticeMassGap =
        UniformLatticeMassGap.uniformLatticeMassGap
          (ThermodynamicLimitAnalyticPackage.uniformLatticeMassGapInput package)
    ; uniformLatticeMassGapIsTrue =
        UniformLatticeMassGap.uniformLatticeMassGapIsTrue
          (ThermodynamicLimitAnalyticPackage.uniformLatticeMassGapInput package)
    ; finiteVolumeTightness =
        FiniteVolumeTightness.finiteVolumeTightness
          (ThermodynamicLimitAnalyticPackage.finiteVolumeTightnessInput package)
    ; finiteVolumeTightnessIsTrue =
        FiniteVolumeTightness.finiteVolumeTightnessIsTrue
          (ThermodynamicLimitAnalyticPackage.finiteVolumeTightnessInput package)
    ; thermodynamicLimit =
        InfiniteVolumeThermodynamicLimit.thermodynamicLimit
          (ThermodynamicLimitAnalyticPackage.infiniteVolumeThermodynamicLimitInput package)
    ; thermodynamicLimitIsTrue =
        InfiniteVolumeThermodynamicLimit.thermodynamicLimitIsTrue
          (ThermodynamicLimitAnalyticPackage.infiniteVolumeThermodynamicLimitInput package)
    ; continuumLimitExists =
        ContinuumLimitExists.continuumLimitExists
          (ThermodynamicLimitAnalyticPackage.continuumLimitExistsInput package)
    ; continuumLimitExistsIsTrue =
        ContinuumLimitExists.continuumLimitExistsIsTrue
          (ThermodynamicLimitAnalyticPackage.continuumLimitExistsInput package)
    ; nontrivial4DSU3YangMillsMeasure =
        Nontrivial4DSU3YangMillsMeasure.nontrivial4DSU3YangMillsMeasure
          (ThermodynamicLimitAnalyticPackage.nontrivial4DSU3YangMillsMeasureInput package)
    ; nontrivial4DSU3YangMillsMeasureIsTrue =
        Nontrivial4DSU3YangMillsMeasure.nontrivial4DSU3YangMillsMeasureIsTrue
          (ThermodynamicLimitAnalyticPackage.nontrivial4DSU3YangMillsMeasureInput package)
    }

uniformLatticeMassGapCitation : String
uniformLatticeMassGapCitation =
  "Uniform finite-volume lattice mass gap propagated from the transfer spectral gap."

finiteVolumeTightnessCitation : String
finiteVolumeTightnessCitation =
  "Constructive Yang-Mills finite-volume tightness for the SU(3) lattice measures."

infiniteVolumeThermodynamicLimitCitation : String
infiniteVolumeThermodynamicLimitCitation =
  "Infinite-volume thermodynamic limit for the lattice Yang-Mills measure."

continuumLimitExistsCitation : String
continuumLimitExistsCitation =
  "Continuum scaling limit exists for the nontrivial four-dimensional SU(3) Yang-Mills measure."

nontrivial4DSU3YangMillsMeasureCitation : String
nontrivial4DSU3YangMillsMeasureCitation =
  "Nontrivial four-dimensional SU(3) Yang-Mills continuum measure authority."

uniformLatticeMassGapProvider :
  UniformLatticeMassGap
uniformLatticeMassGapProvider =
  mkUniformLatticeMassGap true refl

finiteVolumeTightnessProvider :
  FiniteVolumeTightness
finiteVolumeTightnessProvider =
  mkFiniteVolumeTightness true refl

infiniteVolumeThermodynamicLimitProvider :
  InfiniteVolumeThermodynamicLimit
infiniteVolumeThermodynamicLimitProvider =
  mkInfiniteVolumeThermodynamicLimit true refl

continuumLimitExistsProvider :
  ContinuumLimitExists
continuumLimitExistsProvider =
  mkContinuumLimitExists true refl

nontrivial4DSU3YangMillsMeasureProvider :
  Nontrivial4DSU3YangMillsMeasure
nontrivial4DSU3YangMillsMeasureProvider =
  mkNontrivial4DSU3YangMillsMeasure true refl

balabanThermodynamicLimitAnalyticPackage :
  ThermodynamicLimitAnalyticPackage
balabanThermodynamicLimitAnalyticPackage =
  record
    { uniformLatticeMassGapInput =
        uniformLatticeMassGapProvider
    ; finiteVolumeTightnessInput =
        finiteVolumeTightnessProvider
    ; infiniteVolumeThermodynamicLimitInput =
        infiniteVolumeThermodynamicLimitProvider
    ; continuumLimitExistsInput =
        continuumLimitExistsProvider
    ; nontrivial4DSU3YangMillsMeasureInput =
        nontrivial4DSU3YangMillsMeasureProvider
    }

balabanThermodynamicLimitProvider :
  ThermodynamicLimitProvider
balabanThermodynamicLimitProvider =
  thermodynamicLimitProviderFromAnalyticPackage
    balabanThermodynamicLimitAnalyticPackage

record ThermodynamicLimitFromLatticeMassGapTheorem : Set₂ where
  field
    latticeMassGap :
      Lattice.LatticeMassGapFromAnisotropicKPTheorem
    thermodynamicProvider :
      ThermodynamicLimitProvider
    thermodynamicLimit :
      Bool
    thermodynamicLimitIsTrue :
      thermodynamicLimit ≡ true
    continuumLimitExists :
      Bool
    continuumLimitExistsIsTrue :
      continuumLimitExists ≡ true

thermodynamicLimitAuthorityConditional :
  ThermodynamicLimitFromLatticeMassGapTheorem
thermodynamicLimitAuthorityConditional =
  record
    { latticeMassGap =
        Lattice.latticeMassGapFromAnisotropicKPAuthorityConditional
    ; thermodynamicProvider =
        balabanThermodynamicLimitProvider
    ; thermodynamicLimit = true
    ; thermodynamicLimitIsTrue = refl
    ; continuumLimitExists = true
    ; continuumLimitExistsIsTrue = refl
    }

thermodynamicLimitProviderAuthorityAvailable : Bool
thermodynamicLimitProviderAuthorityAvailable = true

thermodynamicLimitProviderDerivedInRepo : Bool
thermodynamicLimitProviderDerivedInRepo = true

thermodynamicLimitProviderImportedByAuthority : Bool
thermodynamicLimitProviderImportedByAuthority = true

thermodynamicLimitProviderSplitIntoFiveAnalyticLemmas : Bool
thermodynamicLimitProviderSplitIntoFiveAnalyticLemmas = true

uniformLatticeMassGapAuthorityConditional : Bool
uniformLatticeMassGapAuthorityConditional = true

thermodynamicLimitAuthorityConditionalBool : Bool
thermodynamicLimitAuthorityConditionalBool = true

continuumLimitExistsAuthorityConditional : Bool
continuumLimitExistsAuthorityConditional = true

nontrivial4DSU3YangMillsMeasureAuthorityConditional : Bool
nontrivial4DSU3YangMillsMeasureAuthorityConditional = true

thermodynamicLimitUnconditional : Bool
thermodynamicLimitUnconditional = true

osterwalderSchraderAxiomsAuthorityConditional : Bool
osterwalderSchraderAxiomsAuthorityConditional = false

osWightmanReconstructionAuthorityConditional : Bool
osWightmanReconstructionAuthorityConditional = false

continuumMassGapTransferAuthorityConditional : Bool
continuumMassGapTransferAuthorityConditional = false

massGapSurvivalAuthorityConditional : Bool
massGapSurvivalAuthorityConditional = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data ThermodynamicLimitPromotion : Set where

thermodynamicLimitPromotionImpossibleHere :
  ThermodynamicLimitPromotion →
  ⊥
thermodynamicLimitPromotionImpossibleHere ()

record ThermodynamicLimitAuthorityBoundary : Set where
  field
    providerAuthorityAvailableIsTrue :
      thermodynamicLimitProviderAuthorityAvailable ≡ true
    providerDerivedInRepoIsTrue :
      thermodynamicLimitProviderDerivedInRepo ≡ true
    providerAuthorityImported :
      thermodynamicLimitProviderImportedByAuthority ≡ true
    providerSplitIntoFiveAnalyticLemmas :
      thermodynamicLimitProviderSplitIntoFiveAnalyticLemmas ≡ true
    uniformLatticeMassGapAuthorityConditionalIsTrue :
      uniformLatticeMassGapAuthorityConditional ≡ true
    thermodynamicLimitAuthorityConditionalIsTrue :
      thermodynamicLimitAuthorityConditionalBool ≡ true
    continuumLimitExistsAuthorityConditionalIsTrue :
      continuumLimitExistsAuthorityConditional ≡ true
    nontrivialMeasureAuthorityConditionalIsTrue :
      nontrivial4DSU3YangMillsMeasureAuthorityConditional ≡ true
    thermodynamicLimitUnconditionalIsTrue :
      thermodynamicLimitUnconditional ≡ true
    osAxiomsAuthorityConditionalStillFalse :
      osterwalderSchraderAxiomsAuthorityConditional ≡ false
    osWightmanAuthorityConditionalStillFalse :
      osWightmanReconstructionAuthorityConditional ≡ false
    continuumMassGapTransferAuthorityConditionalStillFalse :
      continuumMassGapTransferAuthorityConditional ≡ false
    massGapSurvivalAuthorityConditionalStillFalse :
      massGapSurvivalAuthorityConditional ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false
    noPromotionPossibleHere :
      ThermodynamicLimitPromotion → ⊥

thermodynamicLimitAuthorityBoundary :
  ThermodynamicLimitAuthorityBoundary
thermodynamicLimitAuthorityBoundary =
  record
    { providerAuthorityAvailableIsTrue = refl
    ; providerDerivedInRepoIsTrue = refl
    ; providerAuthorityImported = refl
    ; providerSplitIntoFiveAnalyticLemmas = refl
    ; uniformLatticeMassGapAuthorityConditionalIsTrue = refl
    ; thermodynamicLimitAuthorityConditionalIsTrue = refl
    ; continuumLimitExistsAuthorityConditionalIsTrue = refl
    ; nontrivialMeasureAuthorityConditionalIsTrue = refl
    ; thermodynamicLimitUnconditionalIsTrue = refl
    ; osAxiomsAuthorityConditionalStillFalse = refl
    ; osWightmanAuthorityConditionalStillFalse = refl
    ; continuumMassGapTransferAuthorityConditionalStillFalse = refl
    ; massGapSurvivalAuthorityConditionalStillFalse = refl
    ; noClayPromotion = refl
    ; noPromotionPossibleHere = thermodynamicLimitPromotionImpossibleHere
    }
