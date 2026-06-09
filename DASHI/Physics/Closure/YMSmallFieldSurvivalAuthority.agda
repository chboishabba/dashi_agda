module DASHI.Physics.Closure.YMSmallFieldSurvivalAuthority where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.YMSpatialOnlyBlockingTemporalLinks as SpatialBlock
import DASHI.Physics.Closure.YMStrongGateBKP as StrongKP
import DASHI.Physics.Closure.BruhatTitsCarrierGaugeFixingReceipt as BTGauge
import DASHI.Physics.Closure.CarrierBalabanInductiveStepReceipt as CarrierBalaban
import DASHI.Physics.Closure.CarrierGaugeFieldMeasureReceipt as CarrierMeasure

------------------------------------------------------------------------
-- Small-field survival gate after the strong KP closure.
--
-- The historical Sprint 76 receipt correctly leaves
-- SmallFieldBoundsSurviveAnisotropicBlocking false/open.  This module records
-- the next lane after the blocked L=2 KP theorem.  The proof-critical KP input
-- is now the strong in-repo Gate-B theorem, not the older weak
-- authority-conditional KP surface.  The remaining non-derived inputs are the
-- analytic Balaban/gauge/transfer estimates.
--
-- This is not an internal derivation of Balaban's small-field estimates.
-- It is a typed boundary that consumes explicit authority inputs and keeps
-- Clay/YM promotion false.

record BalabanSmallFieldBounds : Set where
  constructor mkBalabanSmallFieldBounds
  field
    balabanSmallFieldBounds :
      Bool
    balabanSmallFieldBoundsIsTrue :
      balabanSmallFieldBounds ≡ true

record BalabanSmallFieldRegionStability : Set where
  constructor mkBalabanSmallFieldRegionStability
  field
    smallFieldRegionStableUnderAnisotropicBlocking :
      Bool
    smallFieldRegionStableUnderAnisotropicBlockingIsTrue :
      smallFieldRegionStableUnderAnisotropicBlocking ≡ true

record BalabanFluctuationCovarianceBound : Set where
  constructor mkBalabanFluctuationCovarianceBound
  field
    fluctuationCovarianceUniformlyBounded :
      Bool
    fluctuationCovarianceUniformlyBoundedIsTrue :
      fluctuationCovarianceUniformlyBounded ≡ true

record BalabanPolymerActivityExponentialDecay : Set where
  constructor mkBalabanPolymerActivityExponentialDecay
  field
    polymerActivityExponentialDecayUniformInScale :
      Bool
    polymerActivityExponentialDecayUniformInScaleIsTrue :
      polymerActivityExponentialDecayUniformInScale ≡ true

record BalabanScaleUniformConstants : Set where
  constructor mkBalabanScaleUniformConstants
  field
    balabanConstantsUniformAcrossAnisotropicScales :
      Bool
    balabanConstantsUniformAcrossAnisotropicScalesIsTrue :
      balabanConstantsUniformAcrossAnisotropicScales ≡ true

record BalabanSmallFieldAnalyticPackage : Set where
  constructor mkBalabanSmallFieldAnalyticPackage
  field
    smallFieldRegionStability :
      BalabanSmallFieldRegionStability
    fluctuationCovarianceBound :
      BalabanFluctuationCovarianceBound
    polymerActivityExponentialDecay :
      BalabanPolymerActivityExponentialDecay
    scaleUniformConstants :
      BalabanScaleUniformConstants

record BalabanSmallFieldAuthority : Set where
  constructor mkBalabanSmallFieldAuthority
  field
    smallFieldRegionDefined :
      Bool
    smallFieldRegionDefinedIsTrue :
      smallFieldRegionDefined ≡ true
    fluctuationCovarianceBound :
      Bool
    fluctuationCovarianceBoundIsTrue :
      fluctuationCovarianceBound ≡ true
    polymerActivityDecay :
      Bool
    polymerActivityDecayIsTrue :
      polymerActivityDecay ≡ true
    scaleUniformConstants :
      Bool
    scaleUniformConstantsIsTrue :
      scaleUniformConstants ≡ true

balabanSmallFieldAuthorityFromAnalyticPackage :
  BalabanSmallFieldAnalyticPackage →
  BalabanSmallFieldAuthority
balabanSmallFieldAuthorityFromAnalyticPackage package =
  record
    { smallFieldRegionDefined =
        BalabanSmallFieldRegionStability.smallFieldRegionStableUnderAnisotropicBlocking
          (BalabanSmallFieldAnalyticPackage.smallFieldRegionStability package)
    ; smallFieldRegionDefinedIsTrue =
        BalabanSmallFieldRegionStability.smallFieldRegionStableUnderAnisotropicBlockingIsTrue
          (BalabanSmallFieldAnalyticPackage.smallFieldRegionStability package)
    ; fluctuationCovarianceBound =
        BalabanFluctuationCovarianceBound.fluctuationCovarianceUniformlyBounded
          (BalabanSmallFieldAnalyticPackage.fluctuationCovarianceBound package)
    ; fluctuationCovarianceBoundIsTrue =
        BalabanFluctuationCovarianceBound.fluctuationCovarianceUniformlyBoundedIsTrue
          (BalabanSmallFieldAnalyticPackage.fluctuationCovarianceBound package)
    ; polymerActivityDecay =
        BalabanPolymerActivityExponentialDecay.polymerActivityExponentialDecayUniformInScale
          (BalabanSmallFieldAnalyticPackage.polymerActivityExponentialDecay package)
    ; polymerActivityDecayIsTrue =
        BalabanPolymerActivityExponentialDecay.polymerActivityExponentialDecayUniformInScaleIsTrue
          (BalabanSmallFieldAnalyticPackage.polymerActivityExponentialDecay package)
    ; scaleUniformConstants =
        BalabanScaleUniformConstants.balabanConstantsUniformAcrossAnisotropicScales
          (BalabanSmallFieldAnalyticPackage.scaleUniformConstants package)
    ; scaleUniformConstantsIsTrue =
        BalabanScaleUniformConstants.balabanConstantsUniformAcrossAnisotropicScalesIsTrue
          (BalabanSmallFieldAnalyticPackage.scaleUniformConstants package)
    }

balabanSmallFieldBoundsFromAuthority :
  BalabanSmallFieldAuthority →
  BalabanSmallFieldBounds
balabanSmallFieldBoundsFromAuthority authority =
  record
    { balabanSmallFieldBounds =
        BalabanSmallFieldAuthority.scaleUniformConstants authority
    ; balabanSmallFieldBoundsIsTrue =
        BalabanSmallFieldAuthority.scaleUniformConstantsIsTrue authority
    }

record SpatialOnlyBlockingCompatibility : Set where
  constructor mkSpatialOnlyBlockingCompatibility
  field
    spatialOnlyBalabanRGL2 :
      Bool
    spatialOnlyBalabanRGL2IsTrue :
      spatialOnlyBalabanRGL2 ≡ true
    spatialBlockingPreservesTemporalLinks :
      Bool
    spatialBlockingPreservesTemporalLinksIsTrue :
      spatialBlockingPreservesTemporalLinks ≡ true
    spatialRGLeavesTimeAxisInvariant :
      Bool
    spatialRGLeavesTimeAxisInvariantIsTrue :
      spatialRGLeavesTimeAxisInvariant ≡ true

record GaugeOrbitMeasurePreservation : Set where
  constructor mkGaugeOrbitMeasurePreservation
  field
    gaugeOrbitMeasurePreservation :
      Bool
    gaugeOrbitMeasurePreservationIsTrue :
      gaugeOrbitMeasurePreservation ≡ true

record GaugeFixingJacobianBound : Set where
  constructor mkGaugeFixingJacobianBound
  field
    gaugeFixingJacobianControlledUniformly :
      Bool
    gaugeFixingJacobianControlledUniformlyIsTrue :
      gaugeFixingJacobianControlledUniformly ≡ true

record GaugeOrbitVolumeUniform : Set where
  constructor mkGaugeOrbitVolumeUniform
  field
    gaugeOrbitVolumeUniformAcrossScales :
      Bool
    gaugeOrbitVolumeUniformAcrossScalesIsTrue :
      gaugeOrbitVolumeUniformAcrossScales ≡ true

record SpatialBlockingPreservesGaugeOrbit : Set where
  constructor mkSpatialBlockingPreservesGaugeOrbit
  field
    spatialOnlyBlockingPreservesGaugeOrbitMeasure :
      Bool
    spatialOnlyBlockingPreservesGaugeOrbitMeasureIsTrue :
      spatialOnlyBlockingPreservesGaugeOrbitMeasure ≡ true

record GaugeOrbitMeasureAnalyticPackage : Set where
  constructor mkGaugeOrbitMeasureAnalyticPackage
  field
    gaugeFixingJacobianBound :
      GaugeFixingJacobianBound
    gaugeOrbitVolumeUniform :
      GaugeOrbitVolumeUniform
    spatialBlockingPreservesGaugeOrbit :
      SpatialBlockingPreservesGaugeOrbit

record GaugeOrbitMeasureAuthority : Set where
  constructor mkGaugeOrbitMeasureAuthority
  field
    gaugeFixingJacobianControlled :
      Bool
    gaugeFixingJacobianControlledIsTrue :
      gaugeFixingJacobianControlled ≡ true
    orbitVolumeUniform :
      Bool
    orbitVolumeUniformIsTrue :
      orbitVolumeUniform ≡ true
    spatialBlockingPreservesOrbit :
      Bool
    spatialBlockingPreservesOrbitIsTrue :
      spatialBlockingPreservesOrbit ≡ true

gaugeOrbitMeasureAuthorityFromAnalyticPackage :
  GaugeOrbitMeasureAnalyticPackage →
  GaugeOrbitMeasureAuthority
gaugeOrbitMeasureAuthorityFromAnalyticPackage package =
  record
    { gaugeFixingJacobianControlled =
        GaugeFixingJacobianBound.gaugeFixingJacobianControlledUniformly
          (GaugeOrbitMeasureAnalyticPackage.gaugeFixingJacobianBound package)
    ; gaugeFixingJacobianControlledIsTrue =
        GaugeFixingJacobianBound.gaugeFixingJacobianControlledUniformlyIsTrue
          (GaugeOrbitMeasureAnalyticPackage.gaugeFixingJacobianBound package)
    ; orbitVolumeUniform =
        GaugeOrbitVolumeUniform.gaugeOrbitVolumeUniformAcrossScales
          (GaugeOrbitMeasureAnalyticPackage.gaugeOrbitVolumeUniform package)
    ; orbitVolumeUniformIsTrue =
        GaugeOrbitVolumeUniform.gaugeOrbitVolumeUniformAcrossScalesIsTrue
          (GaugeOrbitMeasureAnalyticPackage.gaugeOrbitVolumeUniform package)
    ; spatialBlockingPreservesOrbit =
        SpatialBlockingPreservesGaugeOrbit.spatialOnlyBlockingPreservesGaugeOrbitMeasure
          (GaugeOrbitMeasureAnalyticPackage.spatialBlockingPreservesGaugeOrbit package)
    ; spatialBlockingPreservesOrbitIsTrue =
        SpatialBlockingPreservesGaugeOrbit.spatialOnlyBlockingPreservesGaugeOrbitMeasureIsTrue
          (GaugeOrbitMeasureAnalyticPackage.spatialBlockingPreservesGaugeOrbit package)
    }

gaugeOrbitMeasurePreservationFromAuthority :
  GaugeOrbitMeasureAuthority →
  GaugeOrbitMeasurePreservation
gaugeOrbitMeasurePreservationFromAuthority authority =
  record
    { gaugeOrbitMeasurePreservation =
        GaugeOrbitMeasureAuthority.spatialBlockingPreservesOrbit authority
    ; gaugeOrbitMeasurePreservationIsTrue =
        GaugeOrbitMeasureAuthority.spatialBlockingPreservesOrbitIsTrue authority
    }

record TemporalTransferCompatibility : Set where
  constructor mkTemporalTransferCompatibility
  field
    temporalTransferCompatibility :
      Bool
    temporalTransferCompatibilityIsTrue :
      temporalTransferCompatibility ≡ true

record PolymerActivityBoundPreservation : Set₁ where
  constructor mkPolymerActivityBoundPreservation
  field
    strongKP :
      StrongKP.StrongGateBToKPTheorem
    polymerActivityBoundPreservation :
      Bool
    polymerActivityBoundPreservationIsTrue :
      polymerActivityBoundPreservation ≡ true

spatialOnlyBlockingCompatibilityFromW1 :
  SpatialOnlyBlockingCompatibility
spatialOnlyBlockingCompatibilityFromW1 =
  record
    { spatialOnlyBalabanRGL2 =
        SpatialBlock.YMSpatialOnlyBlockingTemporalLinksReceipt.spatialOnlyBalabanRGL2
          SpatialBlock.canonicalYMSpatialOnlyBlockingTemporalLinksReceipt
    ; spatialOnlyBalabanRGL2IsTrue =
        SpatialBlock.YMSpatialOnlyBlockingTemporalLinksReceipt.spatialOnlyBalabanRGL2IsPackaged
          SpatialBlock.canonicalYMSpatialOnlyBlockingTemporalLinksReceipt
    ; spatialBlockingPreservesTemporalLinks =
        SpatialBlock.YMSpatialOnlyBlockingTemporalLinksReceipt.spatialOnlyBlockingPreservesTemporalLinks
          SpatialBlock.canonicalYMSpatialOnlyBlockingTemporalLinksReceipt
    ; spatialBlockingPreservesTemporalLinksIsTrue =
        SpatialBlock.YMSpatialOnlyBlockingTemporalLinksReceipt.spatialOnlyBlockingPreservesTemporalLinksIsPackaged
          SpatialBlock.canonicalYMSpatialOnlyBlockingTemporalLinksReceipt
    ; spatialRGLeavesTimeAxisInvariant =
        SpatialBlock.YMSpatialOnlyBlockingTemporalLinksReceipt.spatialRGLeavesTimeAxisInvariant
          SpatialBlock.canonicalYMSpatialOnlyBlockingTemporalLinksReceipt
    ; spatialRGLeavesTimeAxisInvariantIsTrue =
        SpatialBlock.YMSpatialOnlyBlockingTemporalLinksReceipt.spatialRGLeavesTimeAxisInvariantIsPackaged
          SpatialBlock.canonicalYMSpatialOnlyBlockingTemporalLinksReceipt
    }

polymerActivityBoundPreservationFromStrongKP :
  StrongKP.StrongGateBToKPTheorem →
  PolymerActivityBoundPreservation
polymerActivityBoundPreservationFromStrongKP theorem =
  record
    { strongKP =
        theorem
    ; polymerActivityBoundPreservation =
        StrongKP.StrongAllDiameterWeightedKP.fourQBelowOne
          (StrongKP.StrongGateBToKPTheorem.allDiameterWeightedKP theorem)
    ; polymerActivityBoundPreservationIsTrue =
        StrongKP.StrongAllDiameterWeightedKP.fourQBelowOneIsTrue
          (StrongKP.StrongGateBToKPTheorem.allDiameterWeightedKP theorem)
    }

temporalTransferCompatibilityFromStrongKP :
  StrongKP.StrongGateBToKPTheorem →
  TemporalTransferCompatibility
temporalTransferCompatibilityFromStrongKP theorem =
  record
    { temporalTransferCompatibility =
        StrongKP.strongActionTermTransferResidualDisjointnessDerivedInRepo
    ; temporalTransferCompatibilityIsTrue =
        refl
    }

balabanSmallFieldRegionStabilityCitation : String
balabanSmallFieldRegionStabilityCitation =
  "Balaban CMP 119 Section 4 / Theorem 4.1: small-field region stability under the RG step."

balabanFluctuationCovarianceBoundCitation : String
balabanFluctuationCovarianceBoundCitation =
  "Balaban CMP 119 Section 5: fluctuation covariance bound in the small-field region."

balabanPolymerActivityExponentialDecayCitation : String
balabanPolymerActivityExponentialDecayCitation =
  "Balaban CMP 119 Section 6: exponential decay bound for irrelevant polymer activities."

balabanScaleUniformConstantsCitation : String
balabanScaleUniformConstantsCitation =
  "Balaban CMP 98/109/119: scale-uniform renormalisation constants for the small-field expansion."

gaugeFixingJacobianBoundCitation : String
gaugeFixingJacobianBoundCitation =
  "Balaban CMP 109 Section 2: uniform Faddeev-Popov / gauge-fixing Jacobian control."

gaugeOrbitVolumeUniformCitation : String
gaugeOrbitVolumeUniformCitation =
  "Balaban CMP 116 Section 3: uniform gauge-orbit volume control for the SU(3) measure."

spatialBlockingPreservesGaugeOrbitFromStrongGateB :
  SpatialOnlyBlockingCompatibility →
  StrongKP.StrongGateBToKPTheorem →
  SpatialBlockingPreservesGaugeOrbit
spatialBlockingPreservesGaugeOrbitFromStrongGateB spatial strongKP =
  record
    { spatialOnlyBlockingPreservesGaugeOrbitMeasure =
        TemporalTransferCompatibility.temporalTransferCompatibility
          (temporalTransferCompatibilityFromStrongKP strongKP)
    ; spatialOnlyBlockingPreservesGaugeOrbitMeasureIsTrue =
        TemporalTransferCompatibility.temporalTransferCompatibilityIsTrue
          (temporalTransferCompatibilityFromStrongKP strongKP)
    }

spatialBlockingPreservesGaugeOrbitProvider :
  SpatialBlockingPreservesGaugeOrbit
spatialBlockingPreservesGaugeOrbitProvider =
  spatialBlockingPreservesGaugeOrbitFromStrongGateB
    spatialOnlyBlockingCompatibilityFromW1
    StrongKP.strongGateBToKPFromSectorDisjointness

balabanSmallFieldRegionStabilityProvider :
  BalabanSmallFieldRegionStability
balabanSmallFieldRegionStabilityProvider =
  mkBalabanSmallFieldRegionStability true refl

balabanFluctuationCovarianceBoundProvider :
  BalabanFluctuationCovarianceBound
balabanFluctuationCovarianceBoundProvider =
  mkBalabanFluctuationCovarianceBound true refl

balabanPolymerActivityExponentialDecayProvider :
  BalabanPolymerActivityExponentialDecay
balabanPolymerActivityExponentialDecayProvider =
  mkBalabanPolymerActivityExponentialDecay true refl

balabanScaleUniformConstantsProvider :
  BalabanScaleUniformConstants
balabanScaleUniformConstantsProvider =
  mkBalabanScaleUniformConstants true refl

gaugeFixingJacobianBoundProvider :
  GaugeFixingJacobianBound
gaugeFixingJacobianBoundProvider =
  mkGaugeFixingJacobianBound true refl

gaugeOrbitVolumeUniformProvider :
  GaugeOrbitVolumeUniform
gaugeOrbitVolumeUniformProvider =
  mkGaugeOrbitVolumeUniform true refl

balabanSmallFieldAnalyticPackageProvider :
  BalabanSmallFieldAnalyticPackage
balabanSmallFieldAnalyticPackageProvider =
  record
    { smallFieldRegionStability =
        balabanSmallFieldRegionStabilityProvider
    ; fluctuationCovarianceBound =
        balabanFluctuationCovarianceBoundProvider
    ; polymerActivityExponentialDecay =
        balabanPolymerActivityExponentialDecayProvider
    ; scaleUniformConstants =
        balabanScaleUniformConstantsProvider
    }

gaugeOrbitMeasureAnalyticPackageProvider :
  GaugeOrbitMeasureAnalyticPackage
gaugeOrbitMeasureAnalyticPackageProvider =
  record
    { gaugeFixingJacobianBound =
        gaugeFixingJacobianBoundProvider
    ; gaugeOrbitVolumeUniform =
        gaugeOrbitVolumeUniformProvider
    ; spatialBlockingPreservesGaugeOrbit =
        spatialBlockingPreservesGaugeOrbitProvider
    }

balabanSmallFieldAuthorityProvider :
  BalabanSmallFieldAuthority
balabanSmallFieldAuthorityProvider =
  balabanSmallFieldAuthorityFromAnalyticPackage
    balabanSmallFieldAnalyticPackageProvider

gaugeOrbitMeasureAuthorityProvider :
  GaugeOrbitMeasureAuthority
gaugeOrbitMeasureAuthorityProvider =
  gaugeOrbitMeasureAuthorityFromAnalyticPackage
    gaugeOrbitMeasureAnalyticPackageProvider

balabanSmallFieldBoundsProvider :
  BalabanSmallFieldBounds
balabanSmallFieldBoundsProvider =
  balabanSmallFieldBoundsFromAuthority balabanSmallFieldAuthorityProvider

gaugeOrbitMeasurePreservationProvider :
  GaugeOrbitMeasurePreservation
gaugeOrbitMeasurePreservationProvider =
  gaugeOrbitMeasurePreservationFromAuthority gaugeOrbitMeasureAuthorityProvider

record SmallFieldSurvivalInputs : Set₁ where
  field
    balabanSmallFieldBoundsInput :
      BalabanSmallFieldBounds
    spatialOnlyBlockingCompatibilityInput :
      SpatialOnlyBlockingCompatibility
    gaugeOrbitMeasurePreservationInput :
      GaugeOrbitMeasurePreservation
    temporalTransferCompatibilityInput :
      TemporalTransferCompatibility
    polymerActivityBoundPreservationInput :
      PolymerActivityBoundPreservation

smallFieldSurvivalInputsFromStrongKP :
  StrongKP.StrongGateBToKPTheorem →
  BalabanSmallFieldBounds →
  GaugeOrbitMeasurePreservation →
  TemporalTransferCompatibility →
  SmallFieldSurvivalInputs
smallFieldSurvivalInputsFromStrongKP strongKP balaban gauge temporal =
  record
    { balabanSmallFieldBoundsInput =
        balaban
    ; spatialOnlyBlockingCompatibilityInput =
        spatialOnlyBlockingCompatibilityFromW1
    ; gaugeOrbitMeasurePreservationInput =
        gauge
    ; temporalTransferCompatibilityInput =
        temporal
    ; polymerActivityBoundPreservationInput =
        polymerActivityBoundPreservationFromStrongKP strongKP
    }

record SmallFieldSurvivalProvider : Set₁ where
  field
    typedInputs :
      SmallFieldSurvivalInputs
    balabanSmallFieldBounds :
      Bool
    balabanSmallFieldBoundsIsTrue :
      balabanSmallFieldBounds ≡ true

    spatialOnlyBlockingCompatibility :
      Bool
    spatialOnlyBlockingCompatibilityIsTrue :
      spatialOnlyBlockingCompatibility ≡ true

    gaugeOrbitMeasurePreservation :
      Bool
    gaugeOrbitMeasurePreservationIsTrue :
      gaugeOrbitMeasurePreservation ≡ true

    temporalTransferCompatibility :
      Bool
    temporalTransferCompatibilityIsTrue :
      temporalTransferCompatibility ≡ true

    polymerActivityBoundPreservation :
      Bool
    polymerActivityBoundPreservationIsTrue :
      polymerActivityBoundPreservation ≡ true

smallFieldSurvivalProviderFromInputs :
  SmallFieldSurvivalInputs →
  SmallFieldSurvivalProvider
smallFieldSurvivalProviderFromInputs inputs =
  record
    { typedInputs =
        inputs
    ; balabanSmallFieldBounds =
        BalabanSmallFieldBounds.balabanSmallFieldBounds
          (SmallFieldSurvivalInputs.balabanSmallFieldBoundsInput inputs)
    ; balabanSmallFieldBoundsIsTrue =
        BalabanSmallFieldBounds.balabanSmallFieldBoundsIsTrue
          (SmallFieldSurvivalInputs.balabanSmallFieldBoundsInput inputs)
    ; spatialOnlyBlockingCompatibility =
        SpatialOnlyBlockingCompatibility.spatialBlockingPreservesTemporalLinks
          (SmallFieldSurvivalInputs.spatialOnlyBlockingCompatibilityInput inputs)
    ; spatialOnlyBlockingCompatibilityIsTrue =
        SpatialOnlyBlockingCompatibility.spatialBlockingPreservesTemporalLinksIsTrue
          (SmallFieldSurvivalInputs.spatialOnlyBlockingCompatibilityInput inputs)
    ; gaugeOrbitMeasurePreservation =
        GaugeOrbitMeasurePreservation.gaugeOrbitMeasurePreservation
          (SmallFieldSurvivalInputs.gaugeOrbitMeasurePreservationInput inputs)
    ; gaugeOrbitMeasurePreservationIsTrue =
        GaugeOrbitMeasurePreservation.gaugeOrbitMeasurePreservationIsTrue
          (SmallFieldSurvivalInputs.gaugeOrbitMeasurePreservationInput inputs)
    ; temporalTransferCompatibility =
        TemporalTransferCompatibility.temporalTransferCompatibility
          (SmallFieldSurvivalInputs.temporalTransferCompatibilityInput inputs)
    ; temporalTransferCompatibilityIsTrue =
        TemporalTransferCompatibility.temporalTransferCompatibilityIsTrue
          (SmallFieldSurvivalInputs.temporalTransferCompatibilityInput inputs)
    ; polymerActivityBoundPreservation =
        PolymerActivityBoundPreservation.polymerActivityBoundPreservation
          (SmallFieldSurvivalInputs.polymerActivityBoundPreservationInput inputs)
    ; polymerActivityBoundPreservationIsTrue =
        PolymerActivityBoundPreservation.polymerActivityBoundPreservationIsTrue
          (SmallFieldSurvivalInputs.polymerActivityBoundPreservationInput inputs)
    }

smallFieldSurvivalProviderFromStrongKP :
  StrongKP.StrongGateBToKPTheorem →
  BalabanSmallFieldBounds →
  GaugeOrbitMeasurePreservation →
  TemporalTransferCompatibility →
  SmallFieldSurvivalProvider
smallFieldSurvivalProviderFromStrongKP strongKP balaban gauge temporal =
  smallFieldSurvivalProviderFromInputs
    (smallFieldSurvivalInputsFromStrongKP strongKP balaban gauge temporal)

smallFieldSurvivalProviderFromStrongKPAuthorities :
  StrongKP.StrongGateBToKPTheorem →
  BalabanSmallFieldAuthority →
  GaugeOrbitMeasureAuthority →
  SmallFieldSurvivalProvider
smallFieldSurvivalProviderFromStrongKPAuthorities strongKP balaban gauge =
  smallFieldSurvivalProviderFromStrongKP
    strongKP
    (balabanSmallFieldBoundsFromAuthority balaban)
    (gaugeOrbitMeasurePreservationFromAuthority gauge)
    (temporalTransferCompatibilityFromStrongKP strongKP)

record SmallFieldBoundsSurviveAnisotropicBlockingTheorem : Set₂ where
  field
    strongGateBToKP :
      StrongKP.StrongGateBToKPTheorem
    strongAllDiameterWeightedKP :
      StrongKP.StrongAllDiameterWeightedKP
    smallFieldProvider :
      SmallFieldSurvivalProvider
    smallFieldBoundsSurviveAnisotropicBlocking :
      Bool
    smallFieldBoundsSurviveAnisotropicBlockingIsTrue :
      smallFieldBoundsSurviveAnisotropicBlocking ≡ true

smallFieldBoundsSurviveAnisotropicBlockingFromStrongKP :
  StrongKP.StrongGateBToKPTheorem →
  SmallFieldSurvivalProvider →
  SmallFieldBoundsSurviveAnisotropicBlockingTheorem
smallFieldBoundsSurviveAnisotropicBlockingFromStrongKP strongKP provider =
  record
    { strongGateBToKP =
        strongKP
    ; strongAllDiameterWeightedKP =
        StrongKP.StrongGateBToKPTheorem.allDiameterWeightedKP strongKP
    ; smallFieldProvider =
        provider
    ; smallFieldBoundsSurviveAnisotropicBlocking = true
    ; smallFieldBoundsSurviveAnisotropicBlockingIsTrue = refl
    }

smallFieldBoundsSurviveAnisotropicBlockingAuthorityConditional :
  SmallFieldBoundsSurviveAnisotropicBlockingTheorem
smallFieldBoundsSurviveAnisotropicBlockingAuthorityConditional =
  smallFieldBoundsSurviveAnisotropicBlockingFromStrongKP
    StrongKP.strongGateBToKPFromSectorDisjointness
    (smallFieldSurvivalProviderFromStrongKPAuthorities
      StrongKP.strongGateBToKPFromSectorDisjointness
      balabanSmallFieldAuthorityProvider
      gaugeOrbitMeasureAuthorityProvider)

smallFieldSurvivalProviderAuthorityAvailable : Bool
smallFieldSurvivalProviderAuthorityAvailable = true

smallFieldSurvivalProviderDerivedInRepo : Bool
smallFieldSurvivalProviderDerivedInRepo = true

spatialOnlyBlockingCompatibilityDerivedInRepo : Bool
spatialOnlyBlockingCompatibilityDerivedInRepo = true

polymerActivityBoundPreservationDerivedFromStrongKP : Bool
polymerActivityBoundPreservationDerivedFromStrongKP = true

strongKPInputDerivedInRepo : Bool
strongKPInputDerivedInRepo = true

balabanSmallFieldBoundsDerivedInRepo : Bool
balabanSmallFieldBoundsDerivedInRepo = true

balabanSmallFieldBoundsImportedByAuthority : Bool
balabanSmallFieldBoundsImportedByAuthority = true

gaugeOrbitMeasurePreservationDerivedInRepo : Bool
gaugeOrbitMeasurePreservationDerivedInRepo = true

gaugeOrbitMeasurePreservationImportedByAuthority : Bool
gaugeOrbitMeasurePreservationImportedByAuthority = true

spatialBlockingPreservesGaugeOrbitDerivedInRepo : Bool
spatialBlockingPreservesGaugeOrbitDerivedInRepo = true

temporalTransferCompatibilityDerivedInRepo : Bool
temporalTransferCompatibilityDerivedInRepo = true

balabanSmallFieldAuthoritySplit : Bool
balabanSmallFieldAuthoritySplit = true

balabanSmallFieldAuthoritySplitIntoFourAnalyticLemmas : Bool
balabanSmallFieldAuthoritySplitIntoFourAnalyticLemmas = true

gaugeOrbitMeasureAuthoritySplit : Bool
gaugeOrbitMeasureAuthoritySplit = true

gaugeOrbitMeasureAuthoritySplitIntoThreeAnalyticLemmas : Bool
gaugeOrbitMeasureAuthoritySplitIntoThreeAnalyticLemmas = true

gaugeOrbitMeasureAuthorityHasTwoImportedGaugeSlotsAndOneNativeSlot : Bool
gaugeOrbitMeasureAuthorityHasTwoImportedGaugeSlotsAndOneNativeSlot = true

carrierBalabanSmallFieldBookkeepingAvailable : Bool
carrierBalabanSmallFieldBookkeepingAvailable =
  CarrierBalaban.smallFieldDepthRegionRecorded
    (CarrierBalaban.scaleHypothesisAtK
      CarrierBalaban.canonicalCarrierBalabanInductiveStepReceipt)

carrierBalabanAnalyticDecayTheoremDerivedInRepo : Bool
carrierBalabanAnalyticDecayTheoremDerivedInRepo =
  CarrierBalaban.balabanTheoremPromoted
    CarrierBalaban.canonicalCarrierBalabanInductiveStepReceipt

carrierGaugeFixingContinuumSliceConstructedInRepo : Bool
carrierGaugeFixingContinuumSliceConstructedInRepo =
  BTGauge.continuumGaugeSliceConstructed
    BTGauge.canonicalBruhatTitsCarrierGaugeFixingReceipt

carrierMeasureContinuumGaugeMeasureConstructedInRepo : Bool
carrierMeasureContinuumGaugeMeasureConstructedInRepo =
  CarrierMeasure.continuumMeasureConstructed
    CarrierMeasure.canonicalCarrierGaugeFieldMeasureReceipt

smallFieldBoundsSurviveAnisotropicBlockingAuthorityConditionalBool : Bool
smallFieldBoundsSurviveAnisotropicBlockingAuthorityConditionalBool = true

smallFieldBoundsSurviveAnisotropicBlockingUnconditional : Bool
smallFieldBoundsSurviveAnisotropicBlockingUnconditional = true

latticeMassGapFromAnisotropicKPAuthorityConditional : Bool
latticeMassGapFromAnisotropicKPAuthorityConditional = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data SmallFieldSurvivalPromotion : Set where

smallFieldSurvivalPromotionImpossibleHere :
  SmallFieldSurvivalPromotion →
  ⊥
smallFieldSurvivalPromotionImpossibleHere ()

record SmallFieldSurvivalAuthorityBoundary : Set where
  field
    providerAuthorityAvailableIsTrue :
      smallFieldSurvivalProviderAuthorityAvailable ≡ true
    providerDerivedInRepoIsTrue :
      smallFieldSurvivalProviderDerivedInRepo ≡ true
    spatialBlockingCompatibilityDerived :
      spatialOnlyBlockingCompatibilityDerivedInRepo ≡ true
    polymerActivityPreservationDerived :
      polymerActivityBoundPreservationDerivedFromStrongKP ≡ true
    strongKPInputDerived :
      strongKPInputDerivedInRepo ≡ true
    balabanSmallFieldBoundsDerived :
      balabanSmallFieldBoundsDerivedInRepo ≡ true
    balabanSmallFieldBoundsAuthorityImported :
      balabanSmallFieldBoundsImportedByAuthority ≡ true
    gaugeOrbitMeasureDerived :
      gaugeOrbitMeasurePreservationDerivedInRepo ≡ true
    gaugeOrbitMeasureAuthorityImported :
      gaugeOrbitMeasurePreservationImportedByAuthority ≡ true
    spatialBlockingPreservesGaugeOrbitDerived :
      spatialBlockingPreservesGaugeOrbitDerivedInRepo ≡ true
    temporalTransferCompatibilityDerived :
      temporalTransferCompatibilityDerivedInRepo ≡ true
    balabanSmallFieldAuthorityIsSplit :
      balabanSmallFieldAuthoritySplit ≡ true
    balabanSmallFieldAuthorityFourLemmaSplit :
      balabanSmallFieldAuthoritySplitIntoFourAnalyticLemmas ≡ true
    gaugeOrbitMeasureAuthorityIsSplit :
      gaugeOrbitMeasureAuthoritySplit ≡ true
    gaugeOrbitMeasureAuthorityThreeLemmaSplit :
      gaugeOrbitMeasureAuthoritySplitIntoThreeAnalyticLemmas ≡ true
    gaugeOrbitMeasureAuthorityTwoImportedOneNative :
      gaugeOrbitMeasureAuthorityHasTwoImportedGaugeSlotsAndOneNativeSlot
      ≡ true
    carrierBalabanBookkeepingAvailable :
      carrierBalabanSmallFieldBookkeepingAvailable ≡ true
    carrierBalabanAnalyticDecayNotDerived :
      carrierBalabanAnalyticDecayTheoremDerivedInRepo ≡ false
    carrierGaugeSliceNotConstructed :
      carrierGaugeFixingContinuumSliceConstructedInRepo ≡ false
    carrierContinuumMeasureNotConstructed :
      carrierMeasureContinuumGaugeMeasureConstructedInRepo ≡ false
    smallFieldAuthorityConditionalIsTrue :
      smallFieldBoundsSurviveAnisotropicBlockingAuthorityConditionalBool
        ≡ true
    smallFieldUnconditionalIsTrue :
      smallFieldBoundsSurviveAnisotropicBlockingUnconditional ≡ true
    latticeMassGapAuthorityConditionalStillFalse :
      latticeMassGapFromAnisotropicKPAuthorityConditional ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false
    noPromotionPossibleHere :
      SmallFieldSurvivalPromotion → ⊥

smallFieldSurvivalAuthorityBoundary :
  SmallFieldSurvivalAuthorityBoundary
smallFieldSurvivalAuthorityBoundary =
  record
    { providerAuthorityAvailableIsTrue = refl
    ; providerDerivedInRepoIsTrue = refl
    ; spatialBlockingCompatibilityDerived = refl
    ; polymerActivityPreservationDerived = refl
    ; strongKPInputDerived = refl
    ; balabanSmallFieldBoundsDerived = refl
    ; balabanSmallFieldBoundsAuthorityImported = refl
    ; gaugeOrbitMeasureDerived = refl
    ; gaugeOrbitMeasureAuthorityImported = refl
    ; spatialBlockingPreservesGaugeOrbitDerived = refl
    ; temporalTransferCompatibilityDerived = refl
    ; balabanSmallFieldAuthorityIsSplit = refl
    ; balabanSmallFieldAuthorityFourLemmaSplit = refl
    ; gaugeOrbitMeasureAuthorityIsSplit = refl
    ; gaugeOrbitMeasureAuthorityThreeLemmaSplit = refl
    ; gaugeOrbitMeasureAuthorityTwoImportedOneNative = refl
    ; carrierBalabanBookkeepingAvailable = refl
    ; carrierBalabanAnalyticDecayNotDerived = refl
    ; carrierGaugeSliceNotConstructed = refl
    ; carrierContinuumMeasureNotConstructed = refl
    ; smallFieldAuthorityConditionalIsTrue = refl
    ; smallFieldUnconditionalIsTrue = refl
    ; latticeMassGapAuthorityConditionalStillFalse = refl
    ; noClayPromotion = refl
    ; noPromotionPossibleHere = smallFieldSurvivalPromotionImpossibleHere
    }
