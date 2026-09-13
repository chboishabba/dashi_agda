module DASHI.Culture.AmyEskridgeAntigravityObservationBidiCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.ViewpointProvenanceBidiExact as V
import DASHI.Culture.AmyEskridgeGravityMechanismCrossPollinationExact as Amy
import DASHI.Culture.AmyEskridgeMechanismAssociationProvenanceExact as Assoc
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

associationForConsumer : ReverseConsumer → Assoc.MechanismAssociationReceipt
associationForConsumer passiveWeightConsumer = Assoc.podkletnovAssociation
associationForConsumer freeFallConsumer = Assoc.liTorrAssociation
associationForConsumer remoteFieldConsumer = Assoc.liTorrAssociation
associationForConsumer inertialResponseConsumer = Assoc.woodwardAssociation
associationForConsumer persistentImpulseConsumer = Assoc.impulsiveAssociation
associationForConsumer metricResponseConsumer = Assoc.metricAssociation

observationRouteForConsumer : ReverseConsumer → Unified.ClaimObservationRoute
observationRouteForConsumer consumer =
  Unified.observationRouteForClaim (claimForConsumer consumer)

------------------------------------------------------------------------
-- Consumer-indexed gravitational projection.  The route proof means this
-- carrier is constructible only when the selected consumer really lands in a
-- gravitational observation channel.  Inertial and momentum consumers remain
-- available upstream but cannot be coerced into this receipt.
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

    associationReceipt : Assoc.MechanismAssociationReceipt
    associationReceiptMatchesConsumer :
      associationForConsumer consumer ≡ associationReceipt
    associationMechanismMatches :
      Assoc.mechanism associationReceipt ≡ historicalMechanism
    associationIsContextualReconstruction :
      Assoc.status associationReceipt ≡ Assoc.dashiContextualReconstruction

    derivedClaim : Anti.AntigravityClaim
    claimMatchesConsumer :
      claimForConsumer consumer ≡ derivedClaim

    materialRegime : Anti.AntigravityMaterialRegime
    request : Anti.AntigravityBidiRequest
    requestClaimMatches : Anti.claim request ≡ derivedClaim
    requestRegimeMatches : Anti.materialRegime request ≡ materialRegime

    observationRoute : Unified.ClaimObservationRoute
    observationRouteMatchesConsumer :
      observationRouteForConsumer consumer ≡ observationRoute
    observationChannel : Obs.GravitationalObservationChannel
    routeIsGravitational :
      observationRoute ≡ Unified.gravitationalObservationRoute observationChannel

    sourceBoundedReading : String
    sourceBoundedReadingMatchesReceipt :
      V.boundedReading viewpointReceipt ≡ sourceBoundedReading

    dashiReconstructionScope : String

open AmyGravityReverseSearchProjection public

amyLiTorrFreeFallProjection : AmyGravityReverseSearchProjection
amyLiTorrFreeFallProjection =
  amy-gravity-reverse-search-projection
    Amy.amyExoticPropulsionReceipt refl
    Amy.canonicalEskridgeMechanismChart refl
    freeFallConsumer
    Gravity.liTorrCoherentGravity refl
    Assoc.liTorrAssociation refl refl refl
    Anti.changedFreeFallResponse refl
    Anti.coherentRegime
    (Anti.antigravity-bidi-request
      Anti.changedFreeFallResponse
      Anti.coherentRegime
      "Amy-associated coherent-superconductor contextual lane; DASHI reverse projection for a free-fall consumer"
      Anti.freeFallDiscriminator
      refl)
    refl refl
    (Unified.gravitationalObservationRoute Obs.freeFallEquivalence) refl
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
    Assoc.liTorrAssociation refl refl refl
    Anti.remoteRepulsiveField refl
    Anti.coherentRegime
    (Anti.antigravity-bidi-request
      Anti.remoteRepulsiveField
      Anti.coherentRegime
      "Amy-associated coherent-superconductor contextual lane; DASHI reverse projection for a remote-field consumer"
      Anti.externalTestMassDiscriminator
      refl)
    refl refl
    (Unified.gravitationalObservationRoute Obs.localTestMassAcceleration) refl
    Obs.localTestMassAcceleration refl
    (V.boundedReading Amy.amyExoticPropulsionReceipt) refl
    "DASHI reconstruction: test whether a coherent-superconductor gravity-family hypothesis predicts a remote external-test-mass acceleration"

------------------------------------------------------------------------
-- Introspective collisions and non-coercion proofs.
------------------------------------------------------------------------

liTorrMechanismCollision :
  mechanismForConsumer Amy.canonicalEskridgeMechanismChart freeFallConsumer
    ≡ mechanismForConsumer Amy.canonicalEskridgeMechanismChart remoteFieldConsumer
liTorrMechanismCollision = refl

freeFallAndRemoteClaimsDistinct :
  claimForConsumer freeFallConsumer ≡ claimForConsumer remoteFieldConsumer → ⊥
freeFallAndRemoteClaimsDistinct ()

freeFallAndRemoteObservationRoutesDistinct :
  observationRouteForConsumer freeFallConsumer
    ≡ observationRouteForConsumer remoteFieldConsumer → ⊥
freeFallAndRemoteObservationRoutesDistinct ()

inertialConsumerDoesNotHaveGravityRoute :
  observationRouteForConsumer inertialResponseConsumer
    ≡ Unified.gravitationalObservationRoute Obs.freeFallEquivalence → ⊥
inertialConsumerDoesNotHaveGravityRoute ()

impulseConsumerDoesNotHaveGravityRoute :
  observationRouteForConsumer persistentImpulseConsumer
    ≡ Unified.gravitationalObservationRoute Obs.localTestMassAcceleration → ⊥
impulseConsumerDoesNotHaveGravityRoute ()

------------------------------------------------------------------------
-- Ordinary-confounder lane stays outside antigravity promotion.
------------------------------------------------------------------------

amyHighVoltageOrdinaryConfounder : Gravity.MechanismFamily
amyHighVoltageOrdinaryConfounder =
  Amy.EskridgeMechanismChart.highVoltageMomentumAlternative
    Amy.canonicalEskridgeMechanismChart

amyHighVoltageAssociation : Assoc.MechanismAssociationReceipt
amyHighVoltageAssociation = Assoc.electrohydrodynamicAssociation

highVoltageConfounderIsElectrohydrodynamic :
  amyHighVoltageOrdinaryConfounder ≡ Gravity.electrohydrodynamicForce
highVoltageConfounderIsElectrohydrodynamic = refl

highVoltageAssociationIsContextual :
  Assoc.status amyHighVoltageAssociation ≡ Assoc.dashiContextualReconstruction
highVoltageAssociationIsContextual = refl

record AmyAntigravityObservationBoundary : Set where
  constructor amy-antigravity-observation-boundary
  field
    amyViewpointReceiptIsPhysicalObservation : Bool
    chartMembershipEqualsAmySourceEntitlement : Bool
    historicalMechanismFamilyUniquelyDeterminesModernClaim : Bool
    everyReverseConsumerIsGravityObservationConsumer : Bool
    dashiReverseProjectionIsAmySourceEntitledClaim : Bool
    sourceReferenceStringIsFullyMigratedAttributedSource : Bool
    consumerSpecificClaimRequired : Bool
    typedObservationRouteRequired : Bool
    ordinaryHighVoltageConfounderMayBePromotedToAntigravity : Bool
    successfulModernExperimentRetroactivelyProvesAmyViewpoint : Bool
    contextualHistoricalAssociationMayNominateReverseSearchRoute : Bool

canonicalAmyAntigravityObservationBoundary : AmyAntigravityObservationBoundary
canonicalAmyAntigravityObservationBoundary =
  amy-antigravity-observation-boundary
    false false false false false false true true false false true
