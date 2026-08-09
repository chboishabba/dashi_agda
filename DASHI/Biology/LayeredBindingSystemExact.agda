module DASHI.Biology.LayeredBindingSystemExact where

open import DASHI.Core.Prelude

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP

------------------------------------------------------------------------
-- Neutral mathematics behind warp/weft/wax vocabulary.
--
-- A layer can contain locally present material and a present binding medium
-- while still failing depth continuity.  Coarse quality control can therefore
-- identify an intact state and a severed-but-bound state.  This is a concrete
-- non-injectivity theorem for the projection, not a materials or safety claim.
------------------------------------------------------------------------

data MaterialPresence : Set where
  materialPresent : MaterialPresence
  materialAbsent : MaterialPresence

data BindingMedium : Set where
  bindingPresent : BindingMedium
  bindingAbsent : BindingMedium

data DepthContinuity : Set where
  depthConnected : DepthContinuity
  depthSevered : DepthContinuity

record BindingState : Set where
  constructor bindingState
  field
    material : MaterialPresence
    medium : BindingMedium
    continuity : DepthContinuity

open BindingState public

data CoarseQC : Set where
  coarseUniform : CoarseQC
  coarseVisibleFailure : CoarseQC

coarseProjection : BindingState → CoarseQC
coarseProjection (bindingState materialPresent bindingPresent depthConnected) =
  coarseUniform
coarseProjection (bindingState materialPresent bindingPresent depthSevered) =
  coarseUniform
coarseProjection (bindingState materialPresent bindingAbsent continuity) =
  coarseVisibleFailure
coarseProjection (bindingState materialAbsent medium continuity) =
  coarseVisibleFailure

intactState : BindingState
intactState =
  bindingState materialPresent bindingPresent depthConnected

severedButBoundState : BindingState
severedButBoundState =
  bindingState materialPresent bindingPresent depthSevered

missingBindingState : BindingState
missingBindingState =
  bindingState materialPresent bindingAbsent depthConnected

intactAndSeveredHaveSameCoarseProjection :
  coarseProjection intactState ≡ coarseProjection severedButBoundState
intactAndSeveredHaveSameCoarseProjection = refl

intactIsNotSeveredButBound :
  intactState ≡ severedButBoundState → ⊥
intactIsNotSeveredButBound ()

missingBindingIsNotSeveredButBound :
  missingBindingState ≡ severedButBoundState → ⊥
missingBindingIsNotSeveredButBound ()

bindingCanBePresentWhileDepthContinuityFails :
  medium severedButBoundState ≡ bindingPresent
  × continuity severedButBoundState ≡ depthSevered
bindingCanBePresentWhileDepthContinuityFails = refl , refl

coarseProjectionIsNotInjective :
  Σ BindingState
    (λ first →
      Σ BindingState
        (λ second →
          coarseProjection first ≡ coarseProjection second
          × (first ≡ second → ⊥)))
coarseProjectionIsNotInjective =
  intactState ,
  (severedButBoundState ,
   (intactAndSeveredHaveSameCoarseProjection , intactIsNotSeveredButBound))

------------------------------------------------------------------------
-- Eight repeated superplies with one distinguished within-superply boundary.
-- The finite model records periodic depth severing independently of lane.
------------------------------------------------------------------------

data Superply : Set where
  superply0 superply1 superply2 superply3 : Superply
  superply4 superply5 superply6 superply7 : Superply

data PlyPosition : Set where
  interiorPly : PlyPosition
  fifteenthPlyBoundary : PlyPosition

periodicLayerState :
  Superply →
  PlyPosition →
  SSP.SSPPrime →
  BindingState
periodicLayerState superply interiorPly lane = intactState
periodicLayerState superply fifteenthPlyBoundary lane = severedButBoundState

boundaryDefectRepeatsAcrossSuperplies :
  (first second : Superply) →
  (lane : SSP.SSPPrime) →
  periodicLayerState first fifteenthPlyBoundary lane
  ≡ periodicLayerState second fifteenthPlyBoundary lane
boundaryDefectRepeatsAcrossSuperplies first second lane = refl

interiorAndBoundaryCanLookUniform :
  (superply : Superply) →
  (lane : SSP.SSPPrime) →
  coarseProjection (periodicLayerState superply interiorPly lane)
  ≡ coarseProjection
      (periodicLayerState superply fifteenthPlyBoundary lane)
interiorAndBoundaryCanLookUniform superply lane = refl

interiorAndBoundaryAreNotSameState :
  (superply : Superply) →
  (lane : SSP.SSPPrime) →
  periodicLayerState superply interiorPly lane
  ≡ periodicLayerState superply fifteenthPlyBoundary lane
  → ⊥
interiorAndBoundaryAreNotSameState superply lane ()

record LayeredBindingSystem (Depth Lane : Set) : Set₁ where
  constructor layeredBindingSystem
  field
    State : Depth → Lane → Set
    project : {depth : Depth} {lane : Lane} → State depth lane → CoarseQC
    materialAt : {depth : Depth} {lane : Lane} → State depth lane → MaterialPresence
    mediumAt : {depth : Depth} {lane : Lane} → State depth lane → BindingMedium
    continuityAt : {depth : Depth} {lane : Lane} → State depth lane → DepthContinuity

open LayeredBindingSystem public

LayerIndex : Set
LayerIndex = Superply × PlyPosition

layerState : LayerIndex → SSP.SSPPrime → Set
layerState index lane = BindingState

canonicalLayeredBindingSystem :
  LayeredBindingSystem LayerIndex SSP.SSPPrime
canonicalLayeredBindingSystem =
  layeredBindingSystem
    layerState
    coarseProjection
    material
    medium
    continuity
