module DASHI.Mathematics.AlgebraicGeometry.HodgeWitnessedProjectiveCycleDonorExact where

------------------------------------------------------------------------
-- WITNESSED PROJECTIVE HYPERPLANE DONOR ON THE EXACT CLAY CARRIER
--
-- ProjectiveSpaceLiteralHyperplanePowerSpanning already returns the correct
-- rational algebraic cycle type and class equality, but the frozen carrier
-- stores finite support and generator algebraicity only as TYPES.
--
-- This owner consumes an inhabited witness for the ONE actual hyperplane
-- generator cycle, transports that witness through literal rational scaling,
-- and pairs it with the exact singular-class reopening theorem.
--
-- Does not assert the global hyperplane spanning premise or a universal
-- primitive projector.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

import DASHI.Mathematics.AlgebraicGeometry.HodgeDecompositionCycleClassExact as Hodge
import DASHI.Mathematics.AlgebraicGeometry.HodgeRationalClassIntersectionExact as Exact
import DASHI.Mathematics.AlgebraicGeometry.HodgeAlgebraicCycleClayCoreExact as Clay
import DASHI.Mathematics.AlgebraicGeometry.HodgeLiteralCycleClassMapBridgeExact as Literal
import DASHI.Mathematics.AlgebraicGeometry.HodgeLiteralCycleWitnessStrengthAuditExact as Witnessed
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceLiteralHodgeReopeningCompilerExact as Projective
import DASHI.Mathematics.AlgebraicGeometry.HodgeProjectiveKnownCycleResidualBridgeExact as Known

------------------------------------------------------------------------
-- A genuine geometric witness for the actual source hyperplane-power cycle
-- is preserved by the scale operation chosen for each rational Hodge class.
------------------------------------------------------------------------

witnessedProjectiveRepresentative :
  ∀ {variety comparison hodge cycleMap codimension}
    (spanning :
      Projective.ProjectiveSpaceLiteralHyperplanePowerSpanning
        {variety = variety}
        {comparison = comparison}
        {hodge = hodge}
        cycleMap codimension)
    (hyperplaneWitness :
      Witnessed.WitnessedRationalAlgebraicCycle
        (Projective.hyperplanePowerCycle spanning))
    (class :
      Hodge.RationalHodgeClass hodge codimension) →
  Witnessed.WitnessedRationalAlgebraicCycle
    (Projective.projectiveSpaceLiteralCycleRepresentative
      spanning class)
witnessedProjectiveRepresentative
    spanning
    hyperplaneWitness
    class =
  Witnessed.witnessedScaleCycle
    (Projective.coefficientOf spanning class)
    hyperplaneWitness

------------------------------------------------------------------------
-- Exact rational-singular reopening plus ACTUAL certificate inhabitants.
------------------------------------------------------------------------

projectiveExactClassWithGeometricWitness :
  ∀ {variety comparison hodge cycleMap codimension}
    (spanning :
      Projective.ProjectiveSpaceLiteralHyperplanePowerSpanning
        {variety = variety}
        {comparison = comparison}
        {hodge = hodge}
        cycleMap codimension)
    (hyperplaneWitness :
      Witnessed.WitnessedRationalAlgebraicCycle
        (Projective.hyperplanePowerCycle spanning))
    (class :
      Exact.RationalHodgeClassExact hodge codimension) →
  Σ
    (Hodge.RationalAlgebraicCycle variety codimension)
    (λ cycle →
      Witnessed.WitnessedRationalAlgebraicCycle cycle
      ×
      (Clay.singularCycleClass
        (Literal.cycleClassBackground cycleMap)
        codimension
        cycle
      ≡ Exact.singularClass class))
projectiveExactClassWithGeometricWitness
    spanning hyperplaneWitness class =
  Projective.projectiveSpaceLiteralCycleRepresentative
    spanning
    (Hodge.rationalHodgeClass (Exact.hodgeComponent class))
  ,
  (witnessedProjectiveRepresentative
    spanning
    hyperplaneWitness
    (Hodge.rationalHodgeClass (Exact.hodgeComponent class))
  ,
  Known.projectiveLiteralRepresentativeHasExactSingularClass
    spanning
    class)

------------------------------------------------------------------------
-- This adds no class-spanning axiom. The certificate on the chosen
-- hyperplane-power cycle must come from independent geometry. A different
-- theorem is needed to split arbitrary primitive classes into a known
-- projective component plus a genuinely easier primitive residual.
------------------------------------------------------------------------
