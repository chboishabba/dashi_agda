module DASHI.Environment.BiocontrolExternalityExperimentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ExperimentalCoordinateDesignExact as Coordinate
import DASHI.Core.IntersectionalNonFactorability as NonFactor

------------------------------------------------------------------------
-- Finite intervention worlds.
------------------------------------------------------------------------

data TargetSuppression : Set where
  targetSuppressed : TargetSuppression

data BiomassFate : Set where
  retainedInWater exportedFromWater : BiomassFate

data OxygenState : Set where
  oxygenLow oxygenRecovered : OxygenState

data CommunityState : Set where
  communityDegraded nativeRecovery : CommunityState

data NutrientResidual : Set where
  nutrientResidualHigh nutrientResidualLow : NutrientResidual

data SeedbankResidual : Set where
  seedbankPersistent seedbankReduced : SeedbankResidual

data NonTargetState : Set where
  nonTargetUnresolved nonTargetPaid : NonTargetState

data AgentInteraction : Set where
  agentIndependent agentInterference : AgentInteraction

record InterventionWorld : Set where
  constructor interventionWorld
  field
    suppression : TargetSuppression
    biomassFate : BiomassFate
    oxygen : OxygenState
    community : CommunityState
    nutrientResidual : NutrientResidual
    seedbankResidual : SeedbankResidual
    nonTarget : NonTargetState
    interaction : AgentInteraction

open InterventionWorld public

oxygenDebtWorld : InterventionWorld
oxygenDebtWorld = interventionWorld
  targetSuppressed retainedInWater oxygenLow communityDegraded
  nutrientResidualHigh seedbankPersistent nonTargetPaid agentIndependent

oxygenRecoveryWorld : InterventionWorld
oxygenRecoveryWorld = interventionWorld
  targetSuppressed exportedFromWater oxygenRecovered nativeRecovery
  nutrientResidualLow seedbankReduced nonTargetPaid agentIndependent

restorationFailureWorld : InterventionWorld
restorationFailureWorld = interventionWorld
  targetSuppressed exportedFromWater oxygenRecovered communityDegraded
  nutrientResidualLow seedbankPersistent nonTargetPaid agentIndependent

restorationRecoveryWorld : InterventionWorld
restorationRecoveryWorld = interventionWorld
  targetSuppressed exportedFromWater oxygenRecovered nativeRecovery
  nutrientResidualLow seedbankReduced nonTargetPaid agentIndependent

------------------------------------------------------------------------
-- Coarse observers and consumers.
------------------------------------------------------------------------

suppressionObserver : InterventionWorld → TargetSuppression
suppressionObserver = suppression

suppressionOxygenObserver : InterventionWorld → TargetSuppression × OxygenState
suppressionOxygenObserver world = suppression world , oxygen world

oxygenConsumer : InterventionWorld → OxygenState
oxygenConsumer = oxygen

restorationConsumer : InterventionWorld → CommunityState
restorationConsumer = community

oxygenWorldsCollapseOnSuppression :
  suppressionObserver oxygenDebtWorld ≡ suppressionObserver oxygenRecoveryWorld
oxygenWorldsCollapseOnSuppression = refl

oxygenWorldsDifferForConsumer :
  oxygenConsumer oxygenDebtWorld ≡ oxygenConsumer oxygenRecoveryWorld → ⊥
oxygenWorldsDifferForConsumer ()

oxygenNonFactorabilityWitness :
  NonFactor.NonFactorabilityWitness suppressionObserver oxygenConsumer
oxygenNonFactorabilityWitness =
  NonFactor.nonFactorabilityWitness
    oxygenDebtWorld
    oxygenRecoveryWorld
    refl
    (λ ())

oxygenDoesNotFactorThroughSuppression :
  NonFactor.FactorsThrough suppressionObserver oxygenConsumer → ⊥
oxygenDoesNotFactorThroughSuppression =
  NonFactor.witnessRulesOutEveryFlatFactorisation oxygenNonFactorabilityWitness

restorationWorldsCollapseOnSuppressionAndOxygen :
  suppressionOxygenObserver restorationFailureWorld
  ≡ suppressionOxygenObserver restorationRecoveryWorld
restorationWorldsCollapseOnSuppressionAndOxygen = refl

restorationWorldsDifferForConsumer :
  restorationConsumer restorationFailureWorld
  ≡ restorationConsumer restorationRecoveryWorld → ⊥
restorationWorldsDifferForConsumer ()

restorationNonFactorabilityWitness :
  NonFactor.NonFactorabilityWitness suppressionOxygenObserver restorationConsumer
restorationNonFactorabilityWitness =
  NonFactor.nonFactorabilityWitness
    restorationFailureWorld
    restorationRecoveryWorld
    refl
    (λ ())

restorationDoesNotFactorThroughSuppressionAndOxygen :
  NonFactor.FactorsThrough suppressionOxygenObserver restorationConsumer → ⊥
restorationDoesNotFactorThroughSuppressionAndOxygen =
  NonFactor.witnessRulesOutEveryFlatFactorisation restorationNonFactorabilityWitness

------------------------------------------------------------------------
-- Experimental coordinate design.
------------------------------------------------------------------------

data ProbeControl : Set where
  observeOnly : ProbeControl

data CoordinateId : Set where
  targetCoordinate : CoordinateId
  biomassFateCoordinate : CoordinateId
  oxygenCoordinate : CoordinateId
  communityCoordinate : CoordinateId
  nutrientCoordinate : CoordinateId
  seedbankCoordinate : CoordinateId
  nonTargetCoordinate : CoordinateId
  interactionCoordinate : CoordinateId

data CoordinateValue : Set where
  targetValue : TargetSuppression → CoordinateValue
  biomassFateValue : BiomassFate → CoordinateValue
  oxygenValue : OxygenState → CoordinateValue
  communityValue : CommunityState → CoordinateValue
  nutrientValue : NutrientResidual → CoordinateValue
  seedbankValue : SeedbankResidual → CoordinateValue
  nonTargetValue : NonTargetState → CoordinateValue
  interactionValue : AgentInteraction → CoordinateValue

data CoordinateDimension : Set where
  targetDimension biomassDimension oxygenDimension communityDimension : CoordinateDimension
  nutrientDimension seedbankDimension evidenceDimension interactionDimension : CoordinateDimension

readCoordinate : CoordinateId → InterventionWorld → CoordinateValue
readCoordinate targetCoordinate world = targetValue (suppression world)
readCoordinate biomassFateCoordinate world = biomassFateValue (biomassFate world)
readCoordinate oxygenCoordinate world = oxygenValue (oxygen world)
readCoordinate communityCoordinate world = communityValue (community world)
readCoordinate nutrientCoordinate world = nutrientValue (nutrientResidual world)
readCoordinate seedbankCoordinate world = seedbankValue (seedbankResidual world)
readCoordinate nonTargetCoordinate world = nonTargetValue (nonTarget world)
readCoordinate interactionCoordinate world = interactionValue (interaction world)

applyProbe : ProbeControl → InterventionWorld → InterventionWorld
applyProbe observeOnly world = world

biocontrolCoordinateDesign :
  Coordinate.ExperimentalCoordinateDesign
    InterventionWorld ProbeControl CoordinateValue CoordinateDimension
biocontrolCoordinateDesign =
  Coordinate.experimentalCoordinateDesign
    CoordinateId role dimension readCoordinate applyProbe
    coordinateReference dimensionReference calibrationReference controlReference
  where
    role : CoordinateId → Coordinate.CoordinateRole
    role targetCoordinate = Coordinate.measuredObservable
    role biomassFateCoordinate = Coordinate.measuredObservable
    role oxygenCoordinate = Coordinate.derivedDiscriminator
    role communityCoordinate = Coordinate.derivedDiscriminator
    role nutrientCoordinate = Coordinate.measuredObservable
    role seedbankCoordinate = Coordinate.nuisanceCoordinate
    role nonTargetCoordinate = Coordinate.measuredObservable
    role interactionCoordinate = Coordinate.nuisanceCoordinate

    dimension : CoordinateId → CoordinateDimension
    dimension targetCoordinate = targetDimension
    dimension biomassFateCoordinate = biomassDimension
    dimension oxygenCoordinate = oxygenDimension
    dimension communityCoordinate = communityDimension
    dimension nutrientCoordinate = nutrientDimension
    dimension seedbankCoordinate = seedbankDimension
    dimension nonTargetCoordinate = evidenceDimension
    dimension interactionCoordinate = interactionDimension

    coordinateReference : CoordinateId → String
    coordinateReference targetCoordinate = "water-hyacinth target suppression"
    coordinateReference biomassFateCoordinate = "retained versus exported plant biomass"
    coordinateReference oxygenCoordinate = "dissolved-oxygen trajectory discriminator"
    coordinateReference communityCoordinate = "replacement-community recovery discriminator"
    coordinateReference nutrientCoordinate = "N/P/C recycling residual"
    coordinateReference seedbankCoordinate = "persistent seedbank residual"
    coordinateReference nonTargetCoordinate = "non-target host evidence"
    coordinateReference interactionCoordinate = "biocontrol-agent interaction coordinate"

    dimensionReference : CoordinateId → String
    dimensionReference targetCoordinate = "target abundance / cover"
    dimensionReference biomassFateCoordinate = "biomass fate"
    dimensionReference oxygenCoordinate = "water-quality oxygen state"
    dimensionReference communityCoordinate = "community transition state"
    dimensionReference nutrientCoordinate = "nutrient residual state"
    dimensionReference seedbankCoordinate = "propagule residual state"
    dimensionReference nonTargetCoordinate = "evidence status"
    dimensionReference interactionCoordinate = "agent interaction state"

    calibrationReference : CoordinateId → String
    calibrationReference targetCoordinate = "field cover / biomass measurement contract"
    calibrationReference biomassFateCoordinate = "export-versus-in-situ fate observation"
    calibrationReference oxygenCoordinate = "dissolved-oxygen measurement / trajectory derivation"
    calibrationReference communityCoordinate = "declared community-composition survey"
    calibrationReference nutrientCoordinate = "LES N/P/C conservation receipt"
    calibrationReference seedbankCoordinate = "seedbank observation / persistence receipt"
    calibrationReference nonTargetCoordinate = "host-range and post-release evidence receipt"
    calibrationReference interactionCoordinate = "agent-density / damage interaction observation"

    controlReference : ProbeControl → String
    controlReference observeOnly = "observational discriminator probe; no deployment authority implied"

------------------------------------------------------------------------
-- Canonical collision / discriminator receipts used by regressions.
------------------------------------------------------------------------

record OxygenCollisionReceipt : Set where
  constructor oxygenCollisionReceipt
  field
    sameSuppression : suppressionObserver oxygenDebtWorld ≡ suppressionObserver oxygenRecoveryWorld
    differentOxygen : oxygenConsumer oxygenDebtWorld ≡ oxygenConsumer oxygenRecoveryWorld → ⊥

canonicalOxygenCollision : OxygenCollisionReceipt
canonicalOxygenCollision = oxygenCollisionReceipt refl (λ ())

record OxygenDiscriminatorReceipt : Set where
  constructor oxygenDiscriminatorReceipt
  field
    separates :
      Coordinate.CoordinateSeparatesCollision
        biocontrolCoordinateDesign suppressionObserver

canonicalOxygenDiscriminator : OxygenDiscriminatorReceipt
canonicalOxygenDiscriminator = oxygenDiscriminatorReceipt record
  { coordinate = oxygenCoordinate
  ; left = oxygenDebtWorld
  ; right = oxygenRecoveryWorld
  ; currentlyCollapsed = refl
  ; coordinateSeparates = λ ()
  }

record RestorationCollisionReceipt : Set where
  constructor restorationCollisionReceipt
  field
    sameSuppressionAndOxygen :
      suppressionOxygenObserver restorationFailureWorld
      ≡ suppressionOxygenObserver restorationRecoveryWorld
    differentCommunity :
      restorationConsumer restorationFailureWorld
      ≡ restorationConsumer restorationRecoveryWorld → ⊥

canonicalRestorationCollision : RestorationCollisionReceipt
canonicalRestorationCollision = restorationCollisionReceipt refl (λ ())

record RestorationDiscriminatorReceipt : Set where
  constructor restorationDiscriminatorReceipt
  field
    separates :
      Coordinate.CoordinateSeparatesCollision
        biocontrolCoordinateDesign suppressionOxygenObserver

canonicalRestorationDiscriminator : RestorationDiscriminatorReceipt
canonicalRestorationDiscriminator = restorationDiscriminatorReceipt record
  { coordinate = communityCoordinate
  ; left = restorationFailureWorld
  ; right = restorationRecoveryWorld
  ; currentlyCollapsed = refl
  ; coordinateSeparates = λ ()
  }

record BiocontrolExternalityBoundary : Set where
  constructor biocontrolExternalityBoundary
  field
    targetSuppressionAlonePaysOxygenConsumer : Bool
    targetSuppressionAlonePaysOxygenConsumerIsFalse :
      targetSuppressionAlonePaysOxygenConsumer ≡ false
    suppressionAndPresentOxygenPayRestorationConsumer : Bool
    suppressionAndPresentOxygenPayRestorationConsumerIsFalse :
      suppressionAndPresentOxygenPayRestorationConsumer ≡ false
    specificityAndEfficacyAutomaticallyPaySystemAdequacy : Bool
    specificityAndEfficacyAutomaticallyPaySystemAdequacyIsFalse :
      specificityAndEfficacyAutomaticallyPaySystemAdequacy ≡ false

canonicalBiocontrolExternalityBoundary : BiocontrolExternalityBoundary
canonicalBiocontrolExternalityBoundary =
  biocontrolExternalityBoundary false refl false refl false refl
