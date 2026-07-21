module DASHI.Physics.YangMills.BalabanClayAnalyticConcreteDefinitions where

------------------------------------------------------------------------
-- Concrete carrier owners named by the analytic inventory.  These definitions
-- fix the dependency shape without choosing analytic witnesses.
------------------------------------------------------------------------

record ConcreteBulkBondField (Bond LieAlgebra : Set) : Set where
  constructor bulkBondField
  field
    value : Bond → LieAlgebra
open ConcreteBulkBondField public

record ConcreteBlockAverageConstraint
    {State : Set}
    (BlockAverageZero : State → Set)
    (state : State) : Set where
  constructor blockAverageConstraint
  field
    blockAverageIsZero : BlockAverageZero state
open ConcreteBlockAverageConstraint public

record ConcretePatchGeometry
    (BoundaryPatch InterfacePatch CornerPatch NestedPatch Bulk : Set) : Set₁ where
  field
    boundaryExtension : BoundaryPatch → Bulk
    boundaryRestriction : Bulk → BoundaryPatch
    interfaceExtension : InterfacePatch → Bulk
    interfaceRestriction : Bulk → InterfacePatch
    cornerExtension : CornerPatch → Bulk
    cornerRestriction : Bulk → CornerPatch
    nestedExtension : NestedPatch → Bulk
    nestedRestriction : Bulk → NestedPatch
open ConcretePatchGeometry public

ConcreteWeightedBondNorm : Set → Set → Set
ConcreteWeightedBondNorm BondField Bound = BondField → Bound

ConcreteWeightedForceNorm : Set → Set → Set
ConcreteWeightedForceNorm Force Bound = Force → Bound

ConcreteLocalParametrix : Set → Set → Set
ConcreteLocalParametrix Index State = Index → State → State

ConcreteResidualOperator : Set → Set → Set
ConcreteResidualOperator Index State = Index → State → State

record ConcreteCriticalBall
    {Index State : Set}
    (InCriticalBall : Index → State → Set)
    (index : Index) (state : State) : Set where
  constructor criticalBallWitness
  field
    inside : InCriticalBall index state
open ConcreteCriticalBall public
