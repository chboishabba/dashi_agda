module DASHI.Core.PathResidualActionRevisionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- PATH-RESIDUAL ACTION REVISION
--
-- Two histories may collapse to one visible endpoint while retaining different
-- path residue.  If the next action consumes that residue, endpoint-only action
-- selection is non-factorable.
------------------------------------------------------------------------

record PathSensitiveDecisionSystem : Set₁ where
  constructor pathSensitiveDecisionSystem
  field
    History Endpoint Residual Action : Set
    endpoint : History → Endpoint
    residual : History → Residual
    chooseFromResidual : Residual → Action

open PathSensitiveDecisionSystem public

record SameEndpointDifferentResidualAction
    (S : PathSensitiveDecisionSystem) : Set where
  constructor sameEndpointDifferentResidualAction
  field
    left right : History S
    sameEndpoint : endpoint S left ≡ endpoint S right
    differentResidual : residual S left ≡ residual S right → ⊥
    differentAction :
      chooseFromResidual S (residual S left)
      ≡ chooseFromResidual S (residual S right) → ⊥

open SameEndpointDifferentResidualAction public

------------------------------------------------------------------------
-- Exact finite fixture.
------------------------------------------------------------------------

data ToyHistory : Set where pathA pathB : ToyHistory
data ToyEndpoint : Set where endpoint3 : ToyEndpoint
data ToyResidual : Set where residue1 residue2 : ToyResidual
data ToyAction : Set where inspectPath holdPath : ToyAction

toyEndpoint : ToyHistory → ToyEndpoint
toyEndpoint pathA = endpoint3
toyEndpoint pathB = endpoint3

toyResidual : ToyHistory → ToyResidual
toyResidual pathA = residue1
toyResidual pathB = residue2

toyChoose : ToyResidual → ToyAction
toyChoose residue1 = inspectPath
toyChoose residue2 = holdPath

toySystem : PathSensitiveDecisionSystem
toySystem =
  pathSensitiveDecisionSystem
    ToyHistory ToyEndpoint ToyResidual ToyAction
    toyEndpoint toyResidual toyChoose

residueDistinct : residue1 ≡ residue2 → ⊥
residueDistinct ()

actionDistinct : inspectPath ≡ holdPath → ⊥
actionDistinct ()

sameEndpointDifferentPathAction : SameEndpointDifferentResidualAction toySystem
sameEndpointDifferentPathAction =
  sameEndpointDifferentResidualAction
    pathA pathB refl residueDistinct actionDistinct

record PathResidualActionBoundary : Set where
  constructor pathResidualActionBoundary
  field
    sameVisibleEndpointErasesPathDependence : Bool
    sameVisibleEndpointErasesPathDependenceIsFalse :
      sameVisibleEndpointErasesPathDependence ≡ false
    endpointAloneAlwaysDeterminesNextAction : Bool
    endpointAloneAlwaysDeterminesNextActionIsFalse :
      endpointAloneAlwaysDeterminesNextAction ≡ false
    retainedPathResidualMayChangeNextAction : Bool
    retainedPathResidualMayChangeNextActionIsTrue :
      retainedPathResidualMayChangeNextAction ≡ true
    pathSensitivityImpliesUniqueUnderlyingMechanism : Bool
    pathSensitivityImpliesUniqueUnderlyingMechanismIsFalse :
      pathSensitivityImpliesUniqueUnderlyingMechanism ≡ false

canonicalPathResidualActionBoundary : PathResidualActionBoundary
canonicalPathResidualActionBoundary =
  pathResidualActionBoundary false refl false refl true refl false refl
