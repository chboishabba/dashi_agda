module DASHI.Biology.Physical.DynamicTissueGraphRewriteExact where

------------------------------------------------------------------------
-- Morphogenesis changes both biological state and the interaction graph that
-- determines future dynamics.  This is a finite graph-rewrite regression, not
-- a calibrated tissue simulator.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

false≢true : false ≢ true
false≢true ()

record TissueGraphState : Set where
  constructor tissueGraphState
  field
    cellCount : Nat
    junctionPresent : Bool
    displaced : Bool
    differentiated : Bool
    attachedToBody : Bool

open TissueGraphState public

data CellAction : Set where
  divide die connect disconnect move differentiate attach : CellAction

rewrite : CellAction → TissueGraphState → TissueGraphState
rewrite divide (tissueGraphState n j p d a) =
  tissueGraphState (suc n) j p d a
rewrite die (tissueGraphState zero j p d a) =
  tissueGraphState zero j p d a
rewrite die (tissueGraphState (suc n) j p d a) =
  tissueGraphState n j p d a
rewrite connect (tissueGraphState n j p d a) =
  tissueGraphState n true p d a
rewrite disconnect (tissueGraphState n j p d a) =
  tissueGraphState n false p d a
rewrite move (tissueGraphState n j p d a) =
  tissueGraphState n j true d a
rewrite differentiate (tissueGraphState n j p d a) =
  tissueGraphState n j p true a
rewrite attach (tissueGraphState n j p d a) =
  tissueGraphState n j p d true

initialGraph : TissueGraphState
initialGraph = tissueGraphState 1 false false false false

dividedGraph : TissueGraphState
dividedGraph = rewrite divide initialGraph

connectedGraph : TissueGraphState
connectedGraph = rewrite connect dividedGraph

divisionChangesVertexCarrier :
  cellCount dividedGraph ≡ 2
divisionChangesVertexCarrier = refl

connectionChangesEdgeCarrier :
  junctionPresent connectedGraph ≡ true
connectionChangesEdgeCarrier = refl

initialHasNoJunction : junctionPresent initialGraph ≡ false
initialHasNoJunction = refl

edgeRewriteChangesGraphObservation :
  junctionPresent initialGraph ≢ junctionPresent (rewrite connect initialGraph)
edgeRewriteChangesGraphObservation = false≢true

------------------------------------------------------------------------
-- A local cell action may simultaneously change state/topology/position.
------------------------------------------------------------------------

record CompoundCellAction : Set where
  constructor compoundCellAction
  field
    stateUpdate : CellAction
    edgeRewrite : CellAction
    nodeRewrite : CellAction
    displacement : CellAction

open CompoundCellAction public

canonicalMorphogeneticAction : CompoundCellAction
canonicalMorphogeneticAction =
  compoundCellAction differentiate connect divide move

applyCompound : CompoundCellAction → TissueGraphState → TissueGraphState
applyCompound a x =
  rewrite (displacement a)
    (rewrite (nodeRewrite a)
      (rewrite (edgeRewrite a)
        (rewrite (stateUpdate a) x)))

compoundActionChangesCellCount :
  cellCount (applyCompound canonicalMorphogeneticAction initialGraph) ≡ 2
compoundActionChangesCellCount = refl

compoundActionCreatesJunction :
  junctionPresent (applyCompound canonicalMorphogeneticAction initialGraph) ≡ true
compoundActionCreatesJunction = refl

compoundActionMovesCellState :
  displaced (applyCompound canonicalMorphogeneticAction initialGraph) ≡ true
compoundActionMovesCellState = refl

compoundActionDifferentiates :
  differentiated (applyCompound canonicalMorphogeneticAction initialGraph) ≡ true
compoundActionDifferentiates = refl

------------------------------------------------------------------------
-- Hand compatibility is a property of graph + state, not morphology alone.
------------------------------------------------------------------------

record IntegratedOrganConstraint (x : TissueGraphState) : Set where
  constructor integratedOrganConstraint
  field
    junctionRequired : junctionPresent x ≡ true
    differentiatedRequired : differentiated x ≡ true
    attachedRequired : attachedToBody x ≡ true

open IntegratedOrganConstraint public

repairIntegratedGraph : TissueGraphState → TissueGraphState
repairIntegratedGraph x = rewrite attach (rewrite differentiate (rewrite connect x))

repairHitsIntegratedConstraint :
  (x : TissueGraphState) → IntegratedOrganConstraint (repairIntegratedGraph x)
repairHitsIntegratedConstraint (tissueGraphState n j p d a) =
  integratedOrganConstraint refl refl refl

-- This is the finite graph-generating-control surface: the target constrains a
-- graph/state pair, while the repair may rewrite edges and cellular identity.
