module DASHI.Chemistry.DrinkingWaterCorrosionMetalReleaseExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.DrinkingWaterDistributionResidualCorrosionBidiExact as Distribution
import DASHI.Chemistry.TransitionKernel as Chemistry

------------------------------------------------------------------------
-- CORROSION PRODUCT / METAL RELEASE SPINE
--
-- Cross-pollinates distribution chemistry with explicit material-source,
-- scale-state and release-mechanism coordinates.  A measured dissolved/total
-- metal concentration is downstream of these coordinates; it is not an alias
-- for any one of them.
------------------------------------------------------------------------

data MetalKind : Set where
  iron
  copper
  lead
  zinc
  manganese
  nickel
  mixedMetal
  : MetalKind

data MetalReleaseMechanism : Set where
  solubleCorrosionRelease
  particulateScaleRelease
  galvanicRelease
  scaleDissolution
  scaleDestabilisation
  hydraulicParticleMobilisation
  unknownOrMixedRelease
  : MetalReleaseMechanism

data ScaleStateKind : Set where
  absentOrUnresolvedScale
  adherentProtectiveScale
  porousReactiveScale
  destabilisedScale
  detachedParticulateScale
  mixedScale
  : ScaleStateKind

record CorrosionMaterialSource : Set where
  constructor corrosionMaterialSource
  field
    materialClass : Distribution.PipeMaterialClass
    componentReference : String
    installationAgeReference : String
    alloyOrMaterialCompositionReference : String
    solderFittingJointReference : String
    galvanicContactReference : String
    provenanceReference : String

open CorrosionMaterialSource public

record CorrosionScaleState : Set₁ where
  constructor corrosionScaleState
  field
    sourceMaterial : CorrosionMaterialSource
    scaleKind : ScaleStateKind
    scaleChemistry : Chemistry.ReactionNetwork
    mineralPhaseReference : String
    oxidationStateReference : String
    carbonatePhosphateSilicateReference : String
    chlorideSulfateReference : String
    pHAlkalinityReference : String
    redoxDissolvedOxygenReference : String
    hydraulicShearReference : String
    scaleCharacterisationReference : String
    validationReference : String

open CorrosionScaleState public

record MetalReleaseState : Set₁ where
  constructor metalReleaseState
  field
    corrosionInterface : Distribution.PipeWaterCorrosionInterface
    scaleState : CorrosionScaleState
    releasedMetal : MetalKind
    mechanism : MetalReleaseMechanism
    dissolvedFractionReference : String
    particulateFractionReference : String
    totalRecoverableReference : String
    releaseFluxReference : String
    stagnationDependenceReference : String
    hydraulicDisturbanceReference : String
    waterChemistryDependenceReference : String
    empiricalValidationReference : String

open MetalReleaseState public

record CorrosionMetalReleaseBoundary : Set where
  constructor corrosionMetalReleaseBoundary
  field
    metalDetectionIdentifiesUniqueSourceMaterial : Bool
    metalDetectionIdentifiesUniqueSourceMaterialIsFalse :
      metalDetectionIdentifiesUniqueSourceMaterial ≡ false

    metalDetectionIdentifiesUniqueReleaseMechanism : Bool
    metalDetectionIdentifiesUniqueReleaseMechanismIsFalse :
      metalDetectionIdentifiesUniqueReleaseMechanism ≡ false

    dissolvedMetalEqualsTotalMetal : Bool
    dissolvedMetalEqualsTotalMetalIsFalse : dissolvedMetalEqualsTotalMetal ≡ false

    protectiveScaleLabelProvesZeroRelease : Bool
    protectiveScaleLabelProvesZeroReleaseIsFalse : protectiveScaleLabelProvesZeroRelease ≡ false

    chloridePresenceDeterminesMetalReleaseRate : Bool
    chloridePresenceDeterminesMetalReleaseRateIsFalse :
      chloridePresenceDeterminesMetalReleaseRate ≡ false

    releaseInferenceNeedsMaterialScaleHydraulicAndChemistryReceipts : Bool
    releaseInferenceNeedsMaterialScaleHydraulicAndChemistryReceiptsIsTrue :
      releaseInferenceNeedsMaterialScaleHydraulicAndChemistryReceipts ≡ true

canonicalCorrosionMetalReleaseBoundary : CorrosionMetalReleaseBoundary
canonicalCorrosionMetalReleaseBoundary =
  corrosionMetalReleaseBoundary
    false refl false refl false refl false refl false refl true refl
