{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsProjectiveRepresentedExpectationConvergenceRound536Exact where

------------------------------------------------------------------------
-- GOAL-1 A3 / ROUND536:
-- FINITE EXPECTATIONS -> WHOLE-PROJECTIVE REPRESENTED INTEGRAL
--
-- Same transport as R509, but through the corrected R535 representation:
-- no selected finite-cutoff extension occurs anywhere in this route.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsPhysicalProjectiveCylinderRepresentationRound535Exact as R535
import DASHI.Physics.YangMills.YangMillsClayRepresentedContinuumRound476Exact as R476
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.BalabanScalarCylinderExpectationLimitExact as Cylinder
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

projectiveRepresentedExpectationConverges :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division family}
    (inputs :
      R535.PhysicalProjectiveCylinderRepresentationInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family)
    observable →
  Cylinder.Converges
    (RealLimit.canonicalCylinderAlgebra limitLaws)
    (λ cutoff →
      Limit.finiteExpectation family cutoff observable)
    (R476.integrate
      (R476.represented (R535.asSourceLimitRepresentation inputs))
      (R476.measure
        (R476.represented (R535.asSourceLimitRepresentation inputs)))
      observable)
projectiveRepresentedExpectationConverges
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
      (R535.asSourceLimitRepresentation inputs)
      observable)
    (Cylinder.selectedConverges
      (Limit.asCylinderLimitData family)
      observable)

projectiveRepresentedPhysicalExpectationConverges :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division family}
    (inputs :
      R535.PhysicalProjectiveCylinderRepresentationInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family)
    observable →
  Cylinder.Converges
    (RealLimit.canonicalCylinderAlgebra limitLaws)
    (λ cutoff →
      Limit.finiteExpectation family cutoff observable)
    (Physical.expectation
      (R476.asPhysicalContinuum
        (R476.represented (R535.asSourceLimitRepresentation inputs)))
      observable)
projectiveRepresentedPhysicalExpectationConverges inputs observable =
  projectiveRepresentedExpectationConverges inputs observable

round536ProjectiveRepresentedConvergenceCompilerLevel : ProofLevel
round536ProjectiveRepresentedConvergenceCompilerLevel = machineChecked

literalRound536AdditionalContinuumConvergenceAnalysisLevel : ProofLevel
literalRound536AdditionalContinuumConvergenceAnalysisLevel = machineChecked
