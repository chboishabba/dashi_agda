module DASHI.Biology.AvianMagnetoreceptionHardProblemResidualV2 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.MagnetoreceptionSurface as Generic
import DASHI.Biology.AvianMagnetoreceptionCueFusion as Fusion

------------------------------------------------------------------------
-- Mechanism-neutral replacement for the older spin/retina-specific residual
-- lattice.  Retinal spin geometry remains one possible branch, but the generic
-- observable chain is now:
--
--   magnetic interaction
--   -> receptor transduction
--   -> afferent representation
--   -> multisensory integration
--   -> orientation/navigation behavior
--   -> phenomenal-content residual.
------------------------------------------------------------------------

data MagnetoreceptionResidualLocation : Set where
  magneticPhysicalInteraction : MagnetoreceptionResidualLocation
  receptorTransduction : MagnetoreceptionResidualLocation
  afferentNeuralRepresentation : MagnetoreceptionResidualLocation
  multisensoryCueIntegration : MagnetoreceptionResidualLocation
  orientationBehaviorReceipt : MagnetoreceptionResidualLocation
  phenomenalContentGap : MagnetoreceptionResidualLocation

data ResidualPromotionStatus : Set where
  sourceConstrainedObservable : ResidualPromotionStatus
  mechanismCandidate : ResidualPromotionStatus
  quotientConstrainedObservable : ResidualPromotionStatus
  blockedPhenomenal : ResidualPromotionStatus

data ResidualMissingPromotion : Set where
  noCompleteReceptorToAfferentMap : ResidualMissingPromotion
  noCompleteAfferentToCentralMap : ResidualMissingPromotion
  noCompleteSensorFusionMap : ResidualMissingPromotion
  noFirstPersonContentCarrier : ResidualMissingPromotion
  noPhenomenalIdentityMap : ResidualMissingPromotion
  noBehaviorToConsciousnessClosure : ResidualMissingPromotion

observableResidualChain : List MagnetoreceptionResidualLocation
observableResidualChain =
  magneticPhysicalInteraction
  ∷ receptorTransduction
  ∷ afferentNeuralRepresentation
  ∷ multisensoryCueIntegration
  ∷ orientationBehaviorReceipt
  ∷ []

blockedResidualChain : List MagnetoreceptionResidualLocation
blockedResidualChain =
  phenomenalContentGap ∷ []

residualStatus :
  MagnetoreceptionResidualLocation ->
  ResidualPromotionStatus
residualStatus magneticPhysicalInteraction = sourceConstrainedObservable
residualStatus receptorTransduction = sourceConstrainedObservable
residualStatus afferentNeuralRepresentation = mechanismCandidate
residualStatus multisensoryCueIntegration = quotientConstrainedObservable
residualStatus orientationBehaviorReceipt = sourceConstrainedObservable
residualStatus phenomenalContentGap = blockedPhenomenal

missingAt :
  MagnetoreceptionResidualLocation ->
  List ResidualMissingPromotion
missingAt magneticPhysicalInteraction = []
missingAt receptorTransduction = []
missingAt afferentNeuralRepresentation =
  noCompleteReceptorToAfferentMap
  ∷ noCompleteAfferentToCentralMap
  ∷ []
missingAt multisensoryCueIntegration =
  noCompleteSensorFusionMap
  ∷ []
missingAt orientationBehaviorReceipt =
  noBehaviorToConsciousnessClosure
  ∷ []
missingAt phenomenalContentGap =
  noCompleteReceptorToAfferentMap
  ∷ noCompleteAfferentToCentralMap
  ∷ noCompleteSensorFusionMap
  ∷ noFirstPersonContentCarrier
  ∷ noPhenomenalIdentityMap
  ∷ noBehaviorToConsciousnessClosure
  ∷ []

record AvianMagnetoreceptionHardProblemResidualV2 : Set₁ where
  field
    mechanismNeutralSurface :
      Generic.MagnetoreceptionSurface

    cueFusionReceipt :
      Fusion.AvianCueFusionReceipt

    promotedChain :
      List MagnetoreceptionResidualLocation

    promotedChainIsCanonical :
      promotedChain ≡ observableResidualChain

    blockedChain :
      List MagnetoreceptionResidualLocation

    blockedChainIsCanonical :
      blockedChain ≡ blockedResidualChain

    afferentResidualStatus :
      ResidualPromotionStatus

    afferentResidualStatusIsCandidate :
      afferentResidualStatus ≡ mechanismCandidate

    multisensoryResidualStatus :
      ResidualPromotionStatus

    multisensoryResidualStatusIsQuotient :
      multisensoryResidualStatus ≡ quotientConstrainedObservable

    phenomenalResidualStatus :
      ResidualPromotionStatus

    phenomenalResidualStatusIsBlocked :
      phenomenalResidualStatus ≡ blockedPhenomenal

    phenomenalMissingPromotion :
      List ResidualMissingPromotion

    phenomenalMissingPromotionIsExact :
      phenomenalMissingPromotion ≡ missingAt phenomenalContentGap

    retinalBranchRequired :
      Bool

    retinalBranchRequiredIsFalse :
      retinalBranchRequired ≡ false

    hepaticBranchExclusive :
      Bool

    hepaticBranchExclusiveIsFalse :
      hepaticBranchExclusive ≡ false

    phenomenalContentRecovered :
      Bool

    phenomenalContentRecoveredIsFalse :
      phenomenalContentRecovered ≡ false

    boundaryReading :
      String

open AvianMagnetoreceptionHardProblemResidualV2 public

canonicalAvianMagnetoreceptionHardProblemResidualV2 :
  AvianMagnetoreceptionHardProblemResidualV2
canonicalAvianMagnetoreceptionHardProblemResidualV2 =
  record
    { mechanismNeutralSurface =
        Generic.canonicalMechanismNeutralMagnetoreceptionSurface
    ; cueFusionReceipt =
        Fusion.canonicalAvianCueFusionReceipt
    ; promotedChain =
        observableResidualChain
    ; promotedChainIsCanonical = refl
    ; blockedChain =
        blockedResidualChain
    ; blockedChainIsCanonical = refl
    ; afferentResidualStatus =
        residualStatus afferentNeuralRepresentation
    ; afferentResidualStatusIsCandidate = refl
    ; multisensoryResidualStatus =
        residualStatus multisensoryCueIntegration
    ; multisensoryResidualStatusIsQuotient = refl
    ; phenomenalResidualStatus =
        residualStatus phenomenalContentGap
    ; phenomenalResidualStatusIsBlocked = refl
    ; phenomenalMissingPromotion =
        missingAt phenomenalContentGap
    ; phenomenalMissingPromotionIsExact = refl
    ; retinalBranchRequired = false
    ; retinalBranchRequiredIsFalse = refl
    ; hepaticBranchExclusive = false
    ; hepaticBranchExclusiveIsFalse = refl
    ; phenomenalContentRecovered = false
    ; phenomenalContentRecoveredIsFalse = refl
    ; boundaryReading =
        "Magnetic interaction, receptor evidence, cue-fusion constraints, and behavior can be promoted at their evidence level while receptor-to-brain closure and phenomenal content remain explicit residuals."
    }
