module DASHI.Physics.Closure.LightTransportFibreClosure where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Light transport as a receipt-gated fibre closure surface.
--
-- This module records only the DASHI-internal receipt surface adjacent to
-- light-transport discussion.  dashiRTX is a separate physically-based
-- raytracing / MDL sparse light-transport prototype, not part of DASHI Agda
-- and not scaffolding for the adelic Sobolev bridge.  The typed latent
-- transport carrier below may be cached, composed, and discharged only under
-- explicit admissibility receipts; it is not a global constant-time renderer
-- theorem.

data LightTransportLayer : Set where
  sceneStateLayer : LightTransportLayer
  unlitViewportLayer : LightTransportLayer
  geometryFibreLayer : LightTransportLayer
  materialFibreLayer : LightTransportLayer
  spectralFibreLayer : LightTransportLayer
  visibilityFibreLayer : LightTransportLayer
  transportClosureLayer : LightTransportLayer
  litViewportLayer : LightTransportLayer

canonicalLightTransportPipeline : List LightTransportLayer
canonicalLightTransportPipeline =
  sceneStateLayer
  ∷ unlitViewportLayer
  ∷ geometryFibreLayer
  ∷ materialFibreLayer
  ∷ spectralFibreLayer
  ∷ visibilityFibreLayer
  ∷ transportClosureLayer
  ∷ litViewportLayer
  ∷ []

data MaterialMixingMode : Set where
  diffuseSplit : MaterialMixingMode
  specularNearPermutation : MaterialMixingMode
  glossyConeMixing : MaterialMixingMode
  spectralColourTransform : MaterialMixingMode
  subsurfaceInternalClosure : MaterialMixingMode
  participatingMediumClosure : MaterialMixingMode

data TransportCompositionShape : Set where
  sequentialBraid : TransportCompositionShape
  commutativeBlend : TransportCompositionShape
  nonCommutativeKnot : TransportCompositionShape
  bidirectionalMeeting : TransportCompositionShape
  cachedClosureChart : TransportCompositionShape

data LightTransportGate : Set where
  energyConservationGate : LightTransportGate
  positivityGate : LightTransportGate
  visibilityCausalityGate : LightTransportGate
  spectralDomainGate : LightTransportGate
  reciprocityWhenRequiredGate : LightTransportGate
  closureReceiptGate : LightTransportGate
  residualDefectGate : LightTransportGate
  mdlSideInfoGate : LightTransportGate

data LightTransportNonPromotionBoundary : Set where
  noGlobalO1PhysicalExactnessClaim : LightTransportNonPromotionBoundary
  noClosureWithoutReceipt : LightTransportNonPromotionBoundary
  noDenoiserEqualsPhysicsClaim : LightTransportNonPromotionBoundary
  noHiddenResidualDiscard : LightTransportNonPromotionBoundary
  noUncountedSideInformation : LightTransportNonPromotionBoundary
  noMaterialLawPromotionWithoutReceipts : LightTransportNonPromotionBoundary

canonicalLightTransportGates : List LightTransportGate
canonicalLightTransportGates =
  energyConservationGate
  ∷ positivityGate
  ∷ visibilityCausalityGate
  ∷ spectralDomainGate
  ∷ reciprocityWhenRequiredGate
  ∷ closureReceiptGate
  ∷ residualDefectGate
  ∷ mdlSideInfoGate
  ∷ []

canonicalLightTransportBoundaries :
  List LightTransportNonPromotionBoundary
canonicalLightTransportBoundaries =
  noGlobalO1PhysicalExactnessClaim
  ∷ noClosureWithoutReceipt
  ∷ noDenoiserEqualsPhysicsClaim
  ∷ noHiddenResidualDiscard
  ∷ noUncountedSideInformation
  ∷ noMaterialLawPromotionWithoutReceipts
  ∷ []

record LightTransportFibreClosure : Set₁ where
  field
    SceneState : Set
    UnlitViewport : Set
    PhotonOrPixelCarrier : Set
    GeometryFibre : Set
    MaterialFibre : Set
    SpectralFibre : Set
    VisibilityFibre : Set
    TransportOperator : Set
    ClosureReceipt : Set
    ResidualDefect : Set
    LitViewport : Set

    baselineViewport :
      SceneState →
      UnlitViewport

    carrierFromViewport :
      UnlitViewport →
      PhotonOrPixelCarrier

    geometryFibre :
      SceneState →
      PhotonOrPixelCarrier →
      GeometryFibre

    materialFibre :
      SceneState →
      GeometryFibre →
      MaterialFibre

    spectralFibre :
      MaterialFibre →
      SpectralFibre

    visibilityFibre :
      SceneState →
      GeometryFibre →
      VisibilityFibre

    mixingMode :
      MaterialFibre →
      MaterialMixingMode

    compositionShape :
      TransportOperator →
      TransportCompositionShape

    closeTransport :
      GeometryFibre →
      MaterialFibre →
      SpectralFibre →
      VisibilityFibre →
      TransportOperator

    applyClosedTransport :
      PhotonOrPixelCarrier →
      TransportOperator →
      LitViewport

    closureReceipt :
      TransportOperator →
      ClosureReceipt

    residualDefect :
      PhotonOrPixelCarrier →
      TransportOperator →
      ResidualDefect

    residualAdmissible :
      ResidualDefect →
      Set

    gateSatisfied :
      ClosureReceipt →
      LightTransportGate →
      Set

    pipeline :
      List LightTransportLayer

    transportReading :
      String

open LightTransportFibreClosure public

litViewportFromScene :
  (surface : LightTransportFibreClosure) →
  SceneState surface →
  LitViewport surface
litViewportFromScene surface scene =
  applyClosedTransport surface carrier operator
  where
    unlit : UnlitViewport surface
    unlit = baselineViewport surface scene

    carrier : PhotonOrPixelCarrier surface
    carrier = carrierFromViewport surface unlit

    geom : GeometryFibre surface
    geom = geometryFibre surface scene carrier

    mat : MaterialFibre surface
    mat = materialFibre surface scene geom

    spec : SpectralFibre surface
    spec = spectralFibre surface mat

    vis : VisibilityFibre surface
    vis = visibilityFibre surface scene geom

    operator : TransportOperator surface
    operator = closeTransport surface geom mat spec vis

record ClosedLightTransportWitness
    (surface : LightTransportFibreClosure) : Set where
  field
    scene :
      SceneState surface

    operator :
      TransportOperator surface

    receipt :
      ClosureReceipt surface

    gates :
      List LightTransportGate

    gatesAreCanonical :
      gates ≡ canonicalLightTransportGates

    closureMatchesOperator :
      closureReceipt surface operator ≡ receipt

    noGlobalO1Claim :
      Bool

    noGlobalO1ClaimIsTrue :
      noGlobalO1Claim ≡ true

    oneShotOnlyWithClosureReceipt :
      Bool

    oneShotOnlyWithClosureReceiptIsTrue :
      oneShotOnlyWithClosureReceipt ≡ true

    witnessReading :
      String

open ClosedLightTransportWitness public

record LightTransportNonPromotionCertificate
    (surface : LightTransportFibreClosure) : Set where
  field
    boundaries :
      List LightTransportNonPromotionBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalLightTransportBoundaries

    globalO1ExactnessPromoted :
      Bool

    globalO1ExactnessPromotedIsFalse :
      globalO1ExactnessPromoted ≡ false

    hiddenResidualDiscarded :
      Bool

    hiddenResidualDiscardedIsFalse :
      hiddenResidualDiscarded ≡ false

    uncountedSideInformation :
      Bool

    uncountedSideInformationIsFalse :
      uncountedSideInformation ≡ false

    certificateReading :
      String

open LightTransportNonPromotionCertificate public

canonicalLightTransportNonPromotionCertificate :
  (surface : LightTransportFibreClosure) →
  LightTransportNonPromotionCertificate surface
canonicalLightTransportNonPromotionCertificate surface =
  record
    { boundaries =
        canonicalLightTransportBoundaries
    ; boundariesAreCanonical =
        refl
    ; globalO1ExactnessPromoted =
        false
    ; globalO1ExactnessPromotedIsFalse =
        refl
    ; hiddenResidualDiscarded =
        false
    ; hiddenResidualDiscardedIsFalse =
        refl
    ; uncountedSideInformation =
        false
    ; uncountedSideInformationIsFalse =
        refl
    ; certificateReading =
        "Closed light transport may be reused or applied in one step only when the operator has a closure receipt, residual defects remain explicit, and side information is counted."
    }
