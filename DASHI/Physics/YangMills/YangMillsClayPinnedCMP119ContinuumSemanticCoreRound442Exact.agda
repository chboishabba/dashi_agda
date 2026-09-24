{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ContinuumSemanticCoreRound442Exact where

------------------------------------------------------------------------
-- ROUND442 / ONE SAME-OBJECT SEMANTIC CORE PAYS BOTH SOURCE-NATIVE A3 FIELDS
--
-- The pinned continuum constructor already fixes:
--
--   finite family
--     -> limit expectation
--     -> continuum expectation-functional measure
--     -> Schwinger-from-that-same-measure.
--
-- R441 isolates the only remaining interpretation theorem on these objects.
-- This module packages that theorem once per group and derives BOTH historical
-- continuum semantic fields.  No caller may choose a second continuum measure
-- or a second Schwinger family.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsContinuumSchwingerFromMeasureExact as Schwinger
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ContinuumSemanticMeaningRound441Exact as R441
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record PinnedCMP119ContinuumSemanticCore
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Hamiltonian Vacuum : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient)
    (S :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Nat Configuration ℝ
          (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          Hilbert Hamiltonian Vacuum))
    : Set₂ where
  field
    family : ∀ group →
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division

    cylinderEncoding :
      Schwinger.CylinderSchwingerEncoding
        (Configuration → ℝ) Position

    continuumMeaning : ∀ group →
      R441.ConcreteCMP119ContinuumSemanticMeaning
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S group
        (family group) cylinderEncoding

open PinnedCMP119ContinuumSemanticCore public

literalContinuumLimit :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      sequenceLimit limitLaws quotient division S}
    (core :
      PinnedCMP119ContinuumSemanticCore
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  Top.IsContinuumLimitOf S group
    (Limit.finiteMeasure (family core group))
    (Limit.continuumMeasure (family core group))
literalContinuumLimit core group =
  R441.literalContinuumLimitFromConcreteExpectationLimit
    (continuumMeaning core group)

literalSchwingerBelongsToContinuumMeasure :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      sequenceLimit limitLaws quotient division S}
    (core :
      PinnedCMP119ContinuumSemanticCore
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  Top.SchwingerBelongsToMeasure S
    (Limit.continuumMeasure (family core group))
    (Schwinger.schwingerFromMeasure
      (cylinderEncoding core)
      (Limit.continuumMeasure (family core group)))
literalSchwingerBelongsToContinuumMeasure core group =
  R441.literalSchwingerBelongsFromConcreteSameMeasure
    (continuumMeaning core group)

round442ConcreteContinuumSemanticCoreCompilerLevel : ProofLevel
round442ConcreteContinuumSemanticCoreCompilerLevel = machineChecked

round442SourceNativeA3SemanticMeaningLevel : ProofLevel
round442SourceNativeA3SemanticMeaningLevel = conditional

round442IndependentContinuumLimitWitnessRequired : Bool
round442IndependentContinuumLimitWitnessRequired = false

round442IndependentSchwingerBelongingWitnessRequired : Bool
round442IndependentSchwingerBelongingWitnessRequired = false
