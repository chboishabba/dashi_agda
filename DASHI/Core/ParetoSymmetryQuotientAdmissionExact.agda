module DASHI.Core.ParetoSymmetryQuotientAdmissionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Pareto
import DASHI.Core.NDimParetoHyperfabricExact as NDim

------------------------------------------------------------------------
-- SEMANTICALLY QUALIFIED SYMMETRY FOR PARETO QUOTIENTS
--
-- A carrier symmetry is not enough to quotient a Pareto search space.
-- To act as a Pareto-order automorphism on the declared semantic chart it must
-- preserve eligibility and every declared objective coordinate.
------------------------------------------------------------------------

record ParetoOrderAutomorphism
    {problem : Pareto.ConsumerMDLProblem}
    (costs : Pareto.CostHyperfabric problem) : Set₁ where
  constructor paretoOrderAutomorphism
  field
    mapModel : Pareto.Model problem → Pareto.Model problem
    inverseModel : Pareto.Model problem → Pareto.Model problem

    mapInverse :
      (model : Pareto.Model problem) →
      mapModel (inverseModel model) ≡ model

    inverseMap :
      (model : Pareto.Model problem) →
      inverseModel (mapModel model) ≡ model

    preservesEligibility :
      (model : Pareto.Model problem) →
      Pareto.Eligible problem model →
      Pareto.Eligible problem (mapModel model)

    reflectsEligibility :
      (model : Pareto.Model problem) →
      Pareto.Eligible problem (mapModel model) →
      Pareto.Eligible problem model

    preservesAxisCost :
      (axis : Pareto.Axis costs) →
      (model : Pareto.Model problem) →
      Pareto.cost costs axis (mapModel model) ≡ Pareto.cost costs axis model

    semanticSymmetryReference : String

open ParetoOrderAutomorphism public

mapsWeakDominance :
  ∀ {problem : Pareto.ConsumerMDLProblem}
    {costs : Pareto.CostHyperfabric problem}
    (symmetry : ParetoOrderAutomorphism costs)
    {left right : Pareto.Model problem} →
  Pareto.WeaklyDominates costs left right →
  Pareto.WeaklyDominates costs
    (mapModel symmetry left)
    (mapModel symmetry right)
mapsWeakDominance symmetry dominates axis
  rewrite preservesAxisCost symmetry axis left
        | preservesAxisCost symmetry axis right =
  dominates axis

------------------------------------------------------------------------
-- Orbit representative receipt.
--
-- This is intentionally local: a representative may replace a candidate only
-- after a supplied Pareto-order automorphism relates them.  No claim is made
-- that all carrier symmetries are semantic symmetries.
------------------------------------------------------------------------

record QualifiedOrbitRepresentative
    {problem : Pareto.ConsumerMDLProblem}
    {costs : Pareto.CostHyperfabric problem}
    (symmetry : ParetoOrderAutomorphism costs)
    (representative member : Pareto.Model problem) : Set where
  constructor qualifiedOrbitRepresentative
  field
    memberIsImage : mapModel symmetry representative ≡ member
    representativeEligible : Pareto.Eligible problem representative
    orbitReference : String

open QualifiedOrbitRepresentative public

record ParetoSymmetryQuotientBoundary : Set where
  constructor paretoSymmetryQuotientBoundary
  field
    geometricSymmetryAutomaticallyPreservesParetoOrder : Bool
    carrierOrbitAutomaticallyPreservesEligibility : Bool
    costCovarianceIsRequiredForParetoQuotient : Bool
    eligibilityPreservationIsRequiredForParetoQuotient : Bool
    validParetoSymmetryMaySupportRepresentativeSearch : Bool
    symmetryQuotientCreatesUniqueOptimum : Bool

canonicalParetoSymmetryQuotientBoundary : ParetoSymmetryQuotientBoundary
canonicalParetoSymmetryQuotientBoundary =
  paretoSymmetryQuotientBoundary false false true true true false

existingNDimBoundary : NDim.NDimParetoHyperfabricBoundary
existingNDimBoundary = NDim.canonicalNDimParetoHyperfabricBoundary
