{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsRepresentedExpectationConvergenceRound509Exact where

------------------------------------------------------------------------
-- GOAL-1 A3 / ROUND509:
-- FINITE CMP119 EXPECTATIONS CONVERGE TO THE REPRESENTED INTEGRAL
--
-- R499 constructs a countably-additive represented continuum measure and proves
--
--   E_infty(F) = integral F dmu_infty.
--
-- The finite family already proves
--
--   E_n(F) -> E_infty(F)
--
-- in the selected real cylinder convergence algebra.  Therefore convergence to
-- the represented integral is compiler output.  The remaining Clay-facing
-- payment is only that THIS convergence theorem means the opaque literal
-- IsContinuumLimitOf predicate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsPhysicalCylinderRepresentationRound499Exact as R499
import DASHI.Physics.YangMills.YangMillsClayRepresentedContinuumRound476Exact as R476
import DASHI.Physics.YangMills.BalabanScalarCylinderExpectationLimitExact as Cylinder
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

representedExpectationConverges :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division family}
    (inputs :
      R499.PhysicalCylinderRepresentationInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family)
    observable →
  Cylinder.Converges
    (RealLimit.canonicalCylinderAlgebra limitLaws)
    (λ cutoff →
      Limit.finiteExpectation family cutoff observable)
    (R476.integrate
      (R476.represented (R499.asSourceLimitRepresentation inputs))
      (R476.measure
        (R476.represented (R499.asSourceLimitRepresentation inputs)))
      observable)
representedExpectationConverges
    {family = family} {limitLaws = limitLaws}
    inputs observable =
  subst
    (λ target →
      Cylinder.Converges
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        (λ cutoff →
          Limit.finiteExpectation family cutoff observable)
        target)
    (R476.sourceLimitIsIntegral
      (R499.asSourceLimitRepresentation inputs)
      observable)
    (Cylinder.selectedConverges
      (Limit.asCylinderLimitData family)
      observable)

representedPhysicalExpectationConverges :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division family}
    (inputs :
      R499.PhysicalCylinderRepresentationInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family)
    observable →
  Cylinder.Converges
    (RealLimit.canonicalCylinderAlgebra limitLaws)
    (λ cutoff →
      Limit.finiteExpectation family cutoff observable)
    (DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact.expectation
      (R476.asPhysicalContinuum
        (R476.represented (R499.asSourceLimitRepresentation inputs)))
      observable)
representedPhysicalExpectationConverges inputs observable =
  representedExpectationConverges inputs observable

round509RepresentedExpectationConvergenceCompilerLevel : ProofLevel
round509RepresentedExpectationConvergenceCompilerLevel = machineChecked

-- The analytic convergence theorem itself is now compiler-owned after R499.
literalRound509FiniteFamilyConvergenceAnalysisLevel : ProofLevel
literalRound509FiniteFamilyConvergenceAnalysisLevel = machineChecked

-- Still open: interpret that exact convergence theorem as the literal Clay
-- IsContinuumLimitOf predicate for the represented continuum object.
literalRound509ContinuumLimitSemanticInterpretationLevel : ProofLevel
literalRound509ContinuumLimitSemanticInterpretationLevel = conditional
