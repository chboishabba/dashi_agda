{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ABSameMeasureExact where

------------------------------------------------------------------------
-- A/B SAME-OBJECT WELD
--
-- A constructs the continuum physical measure directly from the normalized
-- CMP119 finite family.  B's covariance carrier is only an expectation-level
-- view of that same family.  These equalities make the identity explicit:
--
--   A finite expectation = B finite carrier expectation
--   A continuum expectation = B continuum carrier expectation
--
-- No comparison theorem, weak-limit uniqueness theorem, or post-hoc measure
-- identification is required at the A/B boundary.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119CovarianceCarrierExact as Carrier
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

finiteABExpectationSameObject :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      sequenceLimit limitLaws quotient division S}
    (inputs :
      A.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group cutoff observable →
  Physical.normalizedExpectation
    (Limit.finiteMeasure (A.family inputs group) cutoff)
    observable
  ≡
  Gram.expectation
    (Gram.operations (Carrier.cmp119PhysicalMeasureConvergenceData inputs group))
    (Gram.measureSequence
      (Carrier.cmp119PhysicalMeasureConvergenceData inputs group) cutoff)
    observable
finiteABExpectationSameObject inputs group cutoff observable = refl

continuumABExpectationSameObject :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      sequenceLimit limitLaws quotient division S}
    (inputs :
      A.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group observable →
  Physical.expectation
    (Limit.continuumMeasure (A.family inputs group))
    observable
  ≡
  Gram.expectation
    (Gram.operations (Carrier.cmp119PhysicalMeasureConvergenceData inputs group))
    (Gram.continuumMeasure
      (Carrier.cmp119PhysicalMeasureConvergenceData inputs group))
    observable
continuumABExpectationSameObject inputs group observable = refl

pinnedCMP119ABFiniteSameObjectLevel : ProofLevel
pinnedCMP119ABFiniteSameObjectLevel = machineChecked

pinnedCMP119ABContinuumSameObjectLevel : ProofLevel
pinnedCMP119ABContinuumSameObjectLevel = machineChecked
