module DASHI.Topology.TetrationalGateField where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import Ontology.DNA.FixedPointTernaryAndTetration as ExistingTetration

------------------------------------------------------------------------
-- Local threshold symbols.
--
-- These are control labels for one coordinate/packet.  A DASHI state is a
-- field of such labels, not one globally collapsed four-way answer.

data LocalGate : Set where
  retainGate approachGate departGate branchGate : LocalGate

data TransitionKind : Set where
  retainCurrentChart : TransitionKind
  refineWithinChart : TransitionKind
  increaseFibreDimension : TransitionKind
  openTowerLevel : TransitionKind

record GateCoordinate : Set where
  constructor gateCoordinate
  field
    coordinateLabel : String
    localGate : LocalGate
    requestedTransition : TransitionKind

open GateCoordinate public

record GateField : Set where
  constructor gateField
  field
    ambientDimension : Nat
    coordinates : List GateCoordinate

open GateField public

canonicalMixedGateField : GateField
canonicalMixedGateField =
  gateField 3
    ( gateCoordinate "common mode" retainGate retainCurrentChart
    ∷ gateCoordinate "positive sequence" approachGate refineWithinChart
    ∷ gateCoordinate "negative sequence" departGate increaseFibreDimension
    ∷ gateCoordinate "residual packet" branchGate openTowerLevel
    ∷ []
    )

------------------------------------------------------------------------
-- Reuse the repository's already checked finite tetration recurrence.

TowerDimension : Nat → Nat → Nat
TowerDimension = ExistingTetration.tetrate

triadicTowerHeight0 : TowerDimension 3 0 ≡ 1
triadicTowerHeight0 = refl

triadicTowerHeight1 : TowerDimension 3 1 ≡ 3
triadicTowerHeight1 = refl

triadicTowerHeight2 : TowerDimension 3 2 ≡ 27
triadicTowerHeight2 = refl

record TowerTransition : Set where
  constructor towerTransition
  field
    base : Nat
    currentHeight : Nat
    currentDimension : Nat
    nextDimension : Nat
    currentChecks : currentDimension ≡ TowerDimension base currentHeight
    nextChecks : nextDimension ≡ TowerDimension base (suc currentHeight)
    trigger : TransitionKind

triadicHeightOneToTwo : TowerTransition
triadicHeightOneToTwo =
  towerTransition 3 1 3 27 refl refl openTowerLevel

------------------------------------------------------------------------
-- Search breadth, processing breadth, and processing depth are independent.

record ProcessingProfile : Set where
  constructor processingProfile
  field
    searchBreadth : Nat
    processingBreadth : Nat
    processingDepth : Nat
    interpretation : String

open ProcessingProfile public

focusedDeepProfile : ProcessingProfile
focusedDeepProfile =
  processingProfile 1 27 243
    "one search branch, broad internal fibre, deep recursive processing"

wideShallowProfile : ProcessingProfile
wideShallowProfile =
  processingProfile 27 1 1
    "many candidate branches, narrow internal processing, one update layer"

record TetrationalGateBoundary : Set where
  constructor tetrationalGateBoundary
  field
    localGateIsWholeDynamics : Bool
    localGateIsWholeDynamicsIsFalse : localGateIsWholeDynamics ≡ false
    everyThresholdOpensTower : Bool
    everyThresholdOpensTowerIsFalse : everyThresholdOpensTower ≡ false
    universalQuarterAndHalfThresholdsPromoted : Bool
    universalQuarterAndHalfThresholdsPromotedIsFalse :
      universalQuarterAndHalfThresholdsPromoted ≡ false
    interpretation : String

canonicalTetrationalGateBoundary : TetrationalGateBoundary
canonicalTetrationalGateBoundary =
  tetrationalGateBoundary
    false refl
    false refl
    false refl
    "local gates form an n-dimensional field; aggregation may retain, refine, lift dimension, or open a new finite tetration level"
