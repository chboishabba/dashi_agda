module DASHI.Physics.ExoticGravity.SuperconductingGravityCouplingResidualBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SUPERCONDUCTING-GRAVITY RESIDUAL COEFFICIENT
--
-- alpha_SC->grav is a diagnostic parameter, not an asserted new constant.
-- It is only admissible after ordinary GR, EM, mechanical and thermal terms
-- are represented in the same observable and geometry.
------------------------------------------------------------------------

record CouplingResidualModel : Set where
  constructor coupling-residual-model
  field
    superconductingOrderObservable : String
    measuredGravityChannel : String
    ordinaryGRContribution : String
    ordinaryBackgroundContribution : String
    residualDefinition : String
    couplingCoefficient : String

canonicalCouplingResidualModel : CouplingResidualModel
canonicalCouplingResidualModel = coupling-residual-model
  "O_SC: phase/current/order-parameter source observable"
  "R_measured: external free-fall, clock, phase, or gravitomagnetic channel"
  "R_GR"
  "R_EM + R_mechanical + R_thermal"
  "R_residual = R_measured - R_GR - R_EM - R_mechanical - R_thermal"
  "alpha_SC_to_grav defined only from a reproducible scaling R_residual ~ alpha_SC_to_grav * O_SC"

record CouplingPromotionBoundary : Set where
  constructor coupling-promotion-boundary
  field
    nonzeroApparatusForceDefinesAlpha : Bool
    nonzeroApparatusForceDefinesAlphaIsFalse :
      nonzeroApparatusForceDefinesAlpha ≡ false

    phaseOnOffDifferenceDefinesAlphaWithoutBackgroundClosure : Bool
    phaseOnOffDifferenceDefinesAlphaWithoutBackgroundClosureIsFalse :
      phaseOnOffDifferenceDefinesAlphaWithoutBackgroundClosure ≡ false

    externalGravityChannelRequired : Bool
    externalGravityChannelRequiredIsTrue :
      externalGravityChannelRequired ≡ true

    reproducibleScalingRequired : Bool
    reproducibleScalingRequiredIsTrue : reproducibleScalingRequired ≡ true

    ordinaryComparatorRequired : Bool
    ordinaryComparatorRequiredIsTrue : ordinaryComparatorRequired ≡ true

canonicalCouplingPromotionBoundary : CouplingPromotionBoundary
canonicalCouplingPromotionBoundary =
  coupling-promotion-boundary false refl false refl true refl true refl true refl

------------------------------------------------------------------------
-- Discriminator matrix.
------------------------------------------------------------------------

data Discriminator : Set where
  crossCriticalTemperature : Discriminator
  currentAmplitudeSweep : Discriminator
  fieldAmplitudeSweep : Discriminator
  orientationReversal : Discriminator
  sourceProbeDistanceSweep : Discriminator
  vacuumControl : Discriminator
  externalTestMass : Discriminator
  independentClockOrPhaseProbe : Discriminator
  nullMaterialControl : Discriminator

record DiscriminatorRequirement : Set where
  constructor discriminator-requirement
  field
    discriminator : Discriminator
    purpose : String

phaseRequirement : DiscriminatorRequirement
phaseRequirement = discriminator-requirement crossCriticalTemperature
  "tests whether the residual tracks the superconducting phase rather than temperature alone"

externalProbeRequirement : DiscriminatorRequirement
externalProbeRequirement = discriminator-requirement externalTestMass
  "separates a source-generated gravity-channel response from force internal to the apparatus"

distanceRequirement : DiscriminatorRequirement
distanceRequirement = discriminator-requirement sourceProbeDistanceSweep
  "tests a spatial field law rather than a local pickup or vibration artifact"

------------------------------------------------------------------------
-- BIDI state: alpha is the terminal consumer, never the starting assumption.
------------------------------------------------------------------------

data AlphaLeaf : Set where
  sourceObservableLeaf : AlphaLeaf
  externalProbeLeaf : AlphaLeaf
  phaseControlLeaf : AlphaLeaf
  ordinaryGRLeaf : AlphaLeaf
  ordinaryBackgroundLeaf : AlphaLeaf
  reproducibilityLeaf : AlphaLeaf
  scalingLawLeaf : AlphaLeaf
  alphaClosed : AlphaLeaf

record AlphaClosureState : Set where
  constructor alpha-closure-state
  field
    sourceObservableOwned : Bool
    externalProbeOwned : Bool
    phaseControlOwned : Bool
    ordinaryGROwned : Bool
    ordinaryBackgroundOwned : Bool
    replicated : Bool
    scalingLawOwned : Bool

firstOpenAlphaLeaf : AlphaClosureState → AlphaLeaf
firstOpenAlphaLeaf (alpha-closure-state false e p g b r s) = sourceObservableLeaf
firstOpenAlphaLeaf (alpha-closure-state true false p g b r s) = externalProbeLeaf
firstOpenAlphaLeaf (alpha-closure-state true true false g b r s) = phaseControlLeaf
firstOpenAlphaLeaf (alpha-closure-state true true true false b r s) = ordinaryGRLeaf
firstOpenAlphaLeaf (alpha-closure-state true true true true false r s) = ordinaryBackgroundLeaf
firstOpenAlphaLeaf (alpha-closure-state true true true true true false s) = reproducibilityLeaf
firstOpenAlphaLeaf (alpha-closure-state true true true true true true false) = scalingLawLeaf
firstOpenAlphaLeaf (alpha-closure-state true true true true true true true) = alphaClosed

currentAlphaFrontier : AlphaClosureState
currentAlphaFrontier = alpha-closure-state false false false false false false false

currentFirstOpenAlphaLeaf : AlphaLeaf
currentFirstOpenAlphaLeaf = firstOpenAlphaLeaf currentAlphaFrontier
