module DASHI.Physics.Textile.StitchPhysicalFibreBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Textile.TextileMechanicalFibreExact as Mechanics
import DASHI.Topology.TextileStitchHyperfabricExact as Stitch
import DASHI.Topology.TextileStitchOperationalSemanticsExact as Operational

------------------------------------------------------------------------
-- Physical realization of stitch topology.
--
-- Topology and mechanics remain separate coordinates.  A stitch state does
-- not manufacture material constants, loads, friction or failure data; those
-- are supplied by an explicit physical fibre over its loops and anchors.
------------------------------------------------------------------------

StitchMechanicalFibre : Set → Set₁
StitchMechanicalFibre Scalar =
  Mechanics.PhysicalTextileFibre
    Scalar
    Stitch.LoopId
    Stitch.AnchorId

record PhysicalStitchState (Scalar : Set) : Set₁ where
  constructor physical-stitch-state
  field
    topology : Stitch.StitchState
    mechanics : StitchMechanicalFibre Scalar

open PhysicalStitchState public

record PhysicalKnitTransition
    (Scalar : Set)
    {before after : Stitch.StitchState}
    (transition : Operational.KnitTransition before after) : Set₁ where
  constructor physical-knit-transition
  field
    beforeMechanics : StitchMechanicalFibre Scalar
    afterMechanics : StitchMechanicalFibre Scalar

open PhysicalKnitTransition public

record PhysicalCrochetTransition
    (Scalar : Set)
    {before after : Operational.CrochetCompletedState}
    (transition : Operational.CrochetTransition before after) : Set₁ where
  constructor physical-crochet-transition
  field
    beforeMechanics : StitchMechanicalFibre Scalar
    afterMechanics : StitchMechanicalFibre Scalar

open PhysicalCrochetTransition public

record SameTopologyDifferentMechanicalFibre
    {Scalar : Set}
    (first second : PhysicalStitchState Scalar) : Set₁ where
  constructor same-topology-different-mechanical-fibre
  field
    topologyAgrees : topology first ≡ topology second
    mechanicsDiffer : mechanics first ≡ mechanics second → ⊥

open SameTopologyDifferentMechanicalFibre public

sameTopologyDoesNotEraseMechanicalResidual :
  {Scalar : Set}
  (state : Stitch.StitchState) →
  (first second : StitchMechanicalFibre Scalar) →
  (first ≡ second → ⊥) →
  SameTopologyDifferentMechanicalFibre
    (physical-stitch-state state first)
    (physical-stitch-state state second)
sameTopologyDoesNotEraseMechanicalResidual state first second differ =
  same-topology-different-mechanical-fibre refl differ

------------------------------------------------------------------------
-- No constitutive update law is guessed here.  The topology transition and
-- the before/after material states are both retained so a later sourced
-- mechanics law can relate them without changing the construction semantics.
------------------------------------------------------------------------

data TopologyAloneDeterminesMechanicalUpdate : Set where

topologyAloneDoesNotDetermineMechanicalUpdate :
  TopologyAloneDeterminesMechanicalUpdate → ⊥
topologyAloneDoesNotDetermineMechanicalUpdate ()
