module DASHI.Culture.AmyEskridgeAntigravityObservationBidiCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.ViewpointProvenanceBidiExact as V
import DASHI.Culture.AmyEskridgeGravityMechanismCrossPollinationExact as Amy
import DASHI.Physics.ExoticGravity.EngineeredInertialGravitationalBidiExact as Gravity
import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Physics.ExoticGravity.AntigravityUnificationInteractionExact as Unified
import DASHI.Physics.GR.GravitationalObservationBidiExact as Obs

------------------------------------------------------------------------
-- AMY ESKRIDGE x TYPED ANTIGRAVITY / GRAVITATIONAL OBSERVATION BIDI
--
-- Historical/viewpoint evidence is retained as historical context only.
-- Mapping a historically associated mechanism family into a modern typed
-- antigravity claim is a DASHI reverse-search reconstruction, not an assertion
-- that Eskridge used this exact ontology or established the physical claim.
------------------------------------------------------------------------

data ReverseConsumer : Set where
  passiveWeightConsumer : ReverseConsumer
  freeFallConsumer : ReverseConsumer
  remoteFieldConsumer : ReverseConsumer
  inertialResponseConsumer : ReverseConsumer
  persistentImpulseConsumer : ReverseConsumer
  metricResponseConsumer : ReverseConsumer

claimForConsumer : ReverseConsumer → Anti.AntigravityClaim
claimForConsumer passiveWeightConsumer = Anti.reducedPassiveWeight
claimForConsumer freeFallConsumer = Anti.changedFreeFallResponse
claimForConsumer remoteFieldConsumer = Anti.remoteRepulsiveField
claimForConsumer inertialResponseConsumer = Anti.alteredInertialResponse
claimForConsumer persistentImpulseConsumer = Anti.persistentPropulsiveImpulse
claimForConsumer metricResponseConsumer = Anti.engineeredMetricResponse

mechanismForConsumer :
  Amy.EskridgeMechanismChart → ReverseConsumer → Gravity.MechanismFamily
mechanismForConsumer chart passiveWeightConsumer =
  Amy.EskridgeMechanismChart.superconductingWeightAnomaly chart
mechanismForConsumer chart freeFallConsumer =
  Amy.EskridgeMechanismChart.coherentSuperconductorGravity chart
mechanismForConsumer chart remoteFieldConsumer =
  Amy.EskridgeMechanismChart.coherentSuperconductorGravity chart
mechanismForConsumer chart inertialResponseConsumer =
  Amy.EskridgeMechanismChart.machianInertialVariation chart
mechanismForConsumer chart persistentImpulseConsumer =
  Amy.EskridgeMechanismChart.impulsiveSuperconductorMomentum chart
mechanismForConsumer chart metricResponseConsumer =
  Amy.EskridgeMechanismChart.negativeMassOrMetricLane chart

observationChannelForConsumer :
  ReverseConsumer → Obs.GravitationalObservationChannel
observationChannelForConsumer consumer =
  Unified.observationChannelForClaim (claimForConsumer consumer)

------------------------------------------------------------------------
-- Consumer-indexed projection.
------------------------------------------------------------------------

record AmyGravityReverseSearchProjection : Set where
  constructor amy-gravity-reverse-search-projection
  field
    viewpointReceipt : V.ViewpointReceipt
    viewpointReceiptIsCanonical :
      viewpointReceipt ≡ Amy.amyExoticPropulsionReceipt

    mechanismChart : Amy.EskridgeMechanismChart
    mechanismChartIsCanonical :
      mechanismChart ≡ Amy.canonicalEskridgeMechanismChart

    consumer : ReverseConsumer
    historicalMechanism : Gravity.MechanismFamily
    mechanismMatchesConsumer :
      mechanismForConsumer mechanismChart consumer ≡ historicalMechanism

    derivedClaim : Anti.AntigravityClaim
    claimMatchesConsumer :
      claimForConsumer consumer ≡ derivedClaim

    materialRegime : Anti.AntigravityMaterialRegime
    request : Anti.AntigravityBidiRequest
    requestClaimMatches : Anti.claim request ≡ derivedClaim
    requestRegimeMatches : Anti.materialRegime request ≡ materialRegime

    observationChannel : Obs.GravitationalObservationChannel
    observationChannelMatches :
      observationChannelForConsumer consumer ≡ observationChannel

    sourceBoundedReading : String
    sourceBoundedReadingMatchesReceipt :
      V.boundedReading viewpointReceipt ≡ sourceBoundedReading

    dashiReconstructionScope : String

open AmyGravityReverseSearchProjection public

------------------------------------------------------------------------
-- Concrete Li-Torr/coherent-superconductor projections.  The same historical
-- mechanism coordinate reaches two different consumers and therefore two
-- different physical observation channels.
------------------------------------------------------------------------

amyLiTorrFreeFallProjection : AmyGravityReverseSearchProjection
amyLiTorrFreeFallProjection =
  amy-gravity-reverse-search-projection
    Amy.amyExoticPropulsionReceipt refl
    Amy.canonicalEskridgeMechanismChart refl
    freeFallConsumer
    Gravity.liTorrCoherentGravity refl
    Anti.changedFreeFallResponse refl
    Anti.coherentRegime
    (Anti.antigravity-bidi-request
      Anti.changedFreeFallResponse
      Anti.coherentRegime
      "Amy-associated coherent-superconductor historical lane; DASHI reverse projection for a free-fall consumer"
      Anti.freeFallDiscriminator
      refl)
    refl refl
    Obs.freeFallEquivalence refl
    (V.boundedReading Amy.amyExoticPropulsionReceipt) refl
    "DASHI reconstruction: test whether a coherent-superconductor gravity-family hypothesis predicts a changed free-fall response"

amyLiTorrRemoteFieldProjection : AmyGravityReverseSearchProjection
amyLiTorrRemoteFieldProjection =
  amy-gravity-reverse-search-projection
    Amy.amyExoticPropulsionReceipt refl
    Amy.canonicalEskridgeMechanismChart refl
    remoteFieldConsumer
    Gravity.liTorrCoherentGravity refl
    Anti.remoteRepulsiveField refl
    Anti.coherentRegime
    (Anti.antigravity-bidi-request
      Anti.remoteRepulsiveField
      Anti.coherentRegime
      "Amy-associated coherent-superconductor historical lane; DASHI reverse projection for a remote-field consumer"
      Anti.externalTestMassDiscriminator
      refl)
    refl refl
    Obs.localTestMassAcceleration refl
    (V.boundedReading Amy.amyExoticPropulsionReceipt) refl
    "DASHI reconstruction: test whether a coherent-superconductor gravity-family hypothesis predicts a remote external-test-mass acceleration"

------------------------------------------------------------------------
-- Introspective collision: mechanism family alone is too coarse.
------------------------------------------------------------------------

liTorrMechanismCollision :
  mechanismForConsumer Amy.canonicalEskridgeMechanismChart freeFallConsumer
    ≡ mechanismForConsumer Amy.canonicalEskridgeMechanismChart remoteFieldConsumer
liTorrMechanismCollision = refl

freeFallAndRemoteClaimsDistinct :
  claimForConsumer freeFallConsumer ≡ claimForConsumer remoteFieldConsumer → ⊥
freeFallAndRemoteClaimsDistinct ()

freeFallAndRemoteObservationChannelsDistinct :
  observationChannelForConsumer freeFallConsumer
    ≡ observationChannelForConsumer remoteFieldConsumer → ⊥
freeFallAndRemoteObservationChannelsDistinct ()

------------------------------------------------------------------------
-- Ordinary-confounder lane stays outside antigravity promotion.  The existing
-- Amy chart's high-voltage/electrohydrodynamic family is retained as an
-- ordinary momentum/EM alternative, not coerced into an AntigravityClaim.
------------------------------------------------------------------------

amyHighVoltageOrdinaryConfounder : Gravity.MechanismFamily
amyHighVoltageOrdinaryConfounder =
  Amy.EskridgeMechanismChart.highVoltageMomentumAlternative
    Amy.canonicalEskridgeMechanismChart

highVoltageConfounderIsElectrohydrodynamic :
  amyHighVoltageOrdinaryConfounder ≡ Gravity.electrohydrodynamicForce
highVoltageConfounderIsElectrohydrodynamic = refl

------------------------------------------------------------------------
-- Attribution / promotion boundary.
------------------------------------------------------------------------

record AmyAntigravityObservationBoundary : Set where
  constructor amy-antigravity-observation-boundary
  field
    amyViewpointReceiptIsPhysicalObservation : Bool
    historicalMechanismFamilyUniquelyDeterminesModernClaim : Bool
    dashiReverseProjectionIsAmySourceEntitledClaim : Bool
    sourceReferenceStringIsFullyMigratedAttributedSource : Bool
    consumerSpecificClaimRequired : Bool
    typedObservationChannelRequired : Bool
    ordinaryHighVoltageConfounderMayBePromotedToAntigravity : Bool
    successfulModernExperimentRetroactivelyProvesAmyViewpoint : Bool
    amyHistoricalContextMayNominateReverseSearchRoute : Bool

canonicalAmyAntigravityObservationBoundary : AmyAntigravityObservationBoundary
canonicalAmyAntigravityObservationBoundary =
  amy-antigravity-observation-boundary
    false false false false true true false false true
