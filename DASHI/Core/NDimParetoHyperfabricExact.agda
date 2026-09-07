module DASHI.Core.NDimParetoHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Pareto

------------------------------------------------------------------------
-- N-DIMENSIONAL PARETO HYPERFABRIC
--
-- The existing CostHyperfabric is already dimension-agnostic: its Axis field
-- may be any declared index type.  This owner makes that interpretation
-- explicit without defining a second Pareto order.
--
--   x <=_P y  iff  for every declared axis a,
--                   cost a x <= cost a y.
--
-- Dimension is therefore a property of the declared axis family, not of the
-- number of candidates, not of the cardinality of a ternary visualisation,
-- and not of a scalarised objective.
------------------------------------------------------------------------

record NDimParetoView
    {problem : Pareto.ConsumerMDLProblem}
    (costs : Pareto.CostHyperfabric problem) : Set₁ where
  constructor ndimParetoView
  field
    declaredDimension : Nat
    dimensionReceiptReference : String
    axisSemanticReference : Pareto.Axis costs → String
    axisCountValidated : Bool
    visualisationReference : String

open NDimParetoView public

NDimWeaklyDominates :
  ∀ {problem : Pareto.ConsumerMDLProblem} →
  (costs : Pareto.CostHyperfabric problem) →
  Pareto.Model problem → Pareto.Model problem → Set
NDimWeaklyDominates = Pareto.WeaklyDominates

NDimParetoAdmissible :
  ∀ {problem : Pareto.ConsumerMDLProblem} →
  (costs : Pareto.CostHyperfabric problem) →
  Pareto.Model problem → Set₁
NDimParetoAdmissible = Pareto.ParetoAdmissible

------------------------------------------------------------------------
-- Axis restriction / projection.
--
-- A consumer may inspect a declared subfamily of axes.  This does not prove
-- that the omitted coordinates are irrelevant to a different consumer.
------------------------------------------------------------------------

record AxisProjection
    {problem : Pareto.ConsumerMDLProblem}
    (costs : Pareto.CostHyperfabric problem) : Set₁ where
  constructor axisProjection
  field
    ProjectedAxis : Set
    includeAxis : ProjectedAxis → Pareto.Axis costs
    projectedAxisReference : ProjectedAxis → String
    consumerReference : String

open AxisProjection public

ProjectedWeaklyDominates :
  ∀ {problem : Pareto.ConsumerMDLProblem}
    {costs : Pareto.CostHyperfabric problem} →
  AxisProjection costs →
  Pareto.Model problem → Pareto.Model problem → Set
ProjectedWeaklyDominates projection left right =
  (axis : ProjectedAxis projection) →
  Pareto.cost _ (includeAxis projection axis) left ≤
  Pareto.cost _ (includeAxis projection axis) right

fullDominanceImpliesProjected :
  ∀ {problem : Pareto.ConsumerMDLProblem}
    {costs : Pareto.CostHyperfabric problem}
    (projection : AxisProjection costs)
    {left right : Pareto.Model problem} →
  Pareto.WeaklyDominates costs left right →
  ProjectedWeaklyDominates projection left right
fullDominanceImpliesProjected projection dominates axis =
  dominates (includeAxis projection axis)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record NDimParetoHyperfabricBoundary : Set where
  constructor ndimParetoHyperfabricBoundary
  field
    paretoOrderAlreadySupportsArbitraryAxisFamily : Bool
    dimensionEqualsCandidateCount : Bool
    dimensionEqualsVisualisationStateCount : Bool
    projectedDominanceImpliesFullDominanceAutomatically : Bool
    scalarScoreRequiredForParetoComparison : Bool
    axisSemanticsMustRemainApplicationDeclared : Bool

canonicalNDimParetoHyperfabricBoundary : NDimParetoHyperfabricBoundary
canonicalNDimParetoHyperfabricBoundary =
  ndimParetoHyperfabricBoundary true false false false false true

existingParetoBoundary : Pareto.AdmissibleConsumerMDLBoundary
existingParetoBoundary = Pareto.canonicalAdmissibleConsumerMDLBoundary
