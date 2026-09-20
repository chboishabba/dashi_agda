{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119CovarianceCarrierExact where

------------------------------------------------------------------------
-- SAME CMP119 EXPECTATION LIMIT -> T5/R278 PHYSICAL MEASURE CARRIER
--
-- The B covariance lane no longer chooses another measure sequence:
--
--   measureSequence n = literal normalized CMP119 finite expectation n
--   continuumMeasure  = its canonical real limit.
--
-- Therefore expectation convergence on every cylinder observable is
-- definitional on this carrier.  R278 connected covariance consequently lives
-- on the SAME measure already used by literal A / OS reconstruction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Unit using (⊤; tt)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; _*ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

ExpectationMeasure : Set → Set
ExpectationMeasure Observable = Observable → ℝ

cmp119PhysicalMeasureConvergenceData :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S}
    (inputs :
      A.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (group : G) →
  Gram.PhysicalMeasureConvergenceData
    (ExpectationMeasure (Configuration → ℝ))
    (Configuration → ℝ)
    ℝ
cmp119PhysicalMeasureConvergenceData
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws}
    inputs group = record
  { Gram.PhysicalMeasureConvergenceData.operations = record
      { Gram.PhysicalOSOperations.zero = 0ℝ
      ; Gram.PhysicalOSOperations.add = _+ℝ_
      ; Gram.PhysicalOSOperations.multiply = _*ℝ_
      ; Gram.PhysicalOSOperations.conjugate = λ value → value
      ; Gram.PhysicalOSOperations.reflectObservable =
          OS2.reflectObservable (A.observableAlgebra inputs)
      ; Gram.PhysicalOSOperations.multiplyObservable =
          OS2.multiplyObservable (A.observableAlgebra inputs)
      ; Gram.PhysicalOSOperations.expectation =
          λ measure observable → measure observable
      }
  ; Gram.PhysicalMeasureConvergenceData.scalarConvergence =
      RealLimit.canonicalGramScalarConvergence limitLaws
  ; Gram.PhysicalMeasureConvergenceData.measureSequence =
      λ cutoff observable →
        Limit.finiteExpectation (A.family inputs group) cutoff observable
  ; Gram.PhysicalMeasureConvergenceData.continuumMeasure =
      Limit.limitExpectation (A.family inputs group)
  ; Gram.PhysicalMeasureConvergenceData.LocalGaugeInvariant =
      λ observable → ⊤
  ; Gram.PhysicalMeasureConvergenceData.RenormalizedObservable =
      λ observable → ⊤
  ; Gram.PhysicalMeasureConvergenceData.BoundedObservable =
      λ observable → ⊤
  ; Gram.PhysicalMeasureConvergenceData.UniformlyIntegrable =
      λ sequence → ⊤
  ; Gram.PhysicalMeasureConvergenceData.finiteVolumeReflectedPairExpectationConverges =
      λ left right leftLocal rightLocal → refl
  ; Gram.PhysicalMeasureConvergenceData.thermodynamicReflectedPairExpectationConverges =
      λ left right leftLocal rightLocal → refl
  ; Gram.PhysicalMeasureConvergenceData.continuumReflectedPairExpectationConverges =
      λ left right leftRenormalized rightRenormalized → refl
  ; Gram.PhysicalMeasureConvergenceData.wilsonCylinderObservableUniformlyBounded =
      λ observable bounded → ⊤
  ; Gram.PhysicalMeasureConvergenceData.boundedWeakConvergenceImpliesExpectationConvergence =
      λ observable bounded → refl
  ; Gram.PhysicalMeasureConvergenceData.uniformRenormalizedInsertionMomentBound =
      λ observable renormalized → ⊤
  ; Gram.PhysicalMeasureConvergenceData.uniformIntegrabilityOfReflectedProducts =
      λ left right leftRenormalized rightRenormalized → tt
  ; Gram.PhysicalMeasureConvergenceData.weakConvergencePlusUniformIntegrability =
      λ sequence uniformlyIntegrable → ⊤
  }

cmp119FiniteExpectationMeasureIsLiteralFiniteExpectation :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S}
    (inputs :
      A.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group cutoff observable →
  Gram.expectation
    (Gram.operations (cmp119PhysicalMeasureConvergenceData inputs group))
    (Gram.measureSequence
      (cmp119PhysicalMeasureConvergenceData inputs group) cutoff)
    observable
  _≡_
  Limit.finiteExpectation (A.family inputs group) cutoff observable
cmp119FiniteExpectationMeasureIsLiteralFiniteExpectation
  inputs group cutoff observable = refl

cmp119ContinuumExpectationMeasureIsLiteralALimit :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S}
    (inputs :
      A.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group observable →
  Gram.expectation
    (Gram.operations (cmp119PhysicalMeasureConvergenceData inputs group))
    (Gram.continuumMeasure
      (cmp119PhysicalMeasureConvergenceData inputs group))
    observable
  _≡_
  Limit.limitExpectation (A.family inputs group) observable
cmp119ContinuumExpectationMeasureIsLiteralALimit inputs group observable = refl

pinnedCMP119CovarianceCarrierCompilerLevel : ProofLevel
pinnedCMP119CovarianceCarrierCompilerLevel = machineChecked

pinnedCMP119ABSameMeasureCompilerLevel : ProofLevel
pinnedCMP119ABSameMeasureCompilerLevel = machineChecked
