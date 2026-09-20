{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteOS1SystemExact where

------------------------------------------------------------------------
-- LITERAL A / PREFERRED PINNED OS SYSTEM WITH CONCRETE OS1
--
-- The older pinned OS input record accepts OS1 as an arbitrary predicate.
-- This preferred constructor instead defines OS1 to mean invariance of the
-- SAME normalized CMP119 cylinder-limit expectation under a supplied Euclidean
-- action.  Finite expectation invariance at every cutoff compiles to OS1 by
-- scalar-limit uniqueness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsContinuumSchwingerFromMeasureExact as Schwinger
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanCylinderLimitActionInvariantExact as ActionLimit
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as PinnedOS
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record PinnedCMP119ConcreteOS1Inputs
    (CompactSimpleGroup Spacetime Configuration Position
     CurvaturePolynomial LocalOperator OPECoefficient StressTensor
     HilbertSpace Hamiltonian VacuumState EuclideanAction : Set)
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
          CompactSimpleGroup Spacetime Nat Configuration ℝ
          (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          HilbertSpace Hamiltonian VacuumState)) : Set₂ where
  field
    family : ∀ G →
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division

    cylinderEncoding :
      Schwinger.CylinderSchwingerEncoding
        (Configuration → ℝ) Position

    observableAlgebra :
      OS2.CylinderOSAlgebra (Configuration → ℝ)

    finiteReflectionPositive :
      ∀ G cutoff
        (testFamily :
          Gram.PhysicalOSFiniteTestFamily (Configuration → ℝ) ℝ) →
      0ℝ ≤ℝ
        Gram.physicalReflectedGramQuadraticForm
          (OS2.operations observableAlgebra)
          (λ observable →
            Limit.finiteExpectation (family G) cutoff observable)
          testFamily

    euclideanAct :
      EuclideanAction →
      (Configuration → ℝ) →
      (Configuration → ℝ)

    finiteEuclideanInvariant :
      ∀ G cutoff action observable →
      Limit.finiteExpectation (family G) cutoff
        (euclideanAct action observable)
      ≡
      Limit.finiteExpectation (family G) cutoff observable

    OS0Regularity : CompactSimpleGroup → Set
    OS3PermutationSymmetry : CompactSimpleGroup → Set
    OS4Clustering : CompactSimpleGroup → Set
    OS5GrowthControl : CompactSimpleGroup → Set

    os0 : ∀ G → OS0Regularity G
    os3 : ∀ G → OS3PermutationSymmetry G
    os4 : ∀ G → OS4Clustering G
    os5 : ∀ G → OS5GrowthControl G

open PinnedCMP119ConcreteOS1Inputs public

actionInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action
      sequenceLimit limitLaws quotient division S}
    (inputs :
      PinnedCMP119ConcreteOS1Inputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  ActionLimit.CylinderActionInvariantInputs
    (Limit.asCylinderLimitData (family inputs group))
    Action
actionInputs inputs group = record
  { ActionLimit.CylinderActionInvariantInputs.act =
      euclideanAct inputs
  ; ActionLimit.CylinderActionInvariantInputs.finiteActionInvariant =
      finiteEuclideanInvariant inputs group
  }

continuumEuclideanInvariant :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action
      sequenceLimit limitLaws quotient division S}
    (inputs :
      PinnedCMP119ConcreteOS1Inputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group action observable →
  Limit.limitExpectation (family inputs group)
    (euclideanAct inputs action observable)
  ≡
  Limit.limitExpectation (family inputs group) observable
continuumEuclideanInvariant inputs group =
  ActionLimit.continuumActionInvariant (actionInputs inputs group)

asPinnedOSAxiomInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action
      sequenceLimit limitLaws quotient division S} →
  PinnedCMP119ConcreteOS1Inputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S →
  PinnedOS.PinnedCMP119OSAxiomInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S
asPinnedOSAxiomInputs inputs = record
  { PinnedOS.PinnedCMP119OSAxiomInputs.family =
      family inputs
  ; PinnedOS.PinnedCMP119OSAxiomInputs.cylinderEncoding =
      cylinderEncoding inputs
  ; PinnedOS.PinnedCMP119OSAxiomInputs.observableAlgebra =
      observableAlgebra inputs
  ; PinnedOS.PinnedCMP119OSAxiomInputs.finiteReflectionPositive =
      finiteReflectionPositive inputs
  ; PinnedOS.PinnedCMP119OSAxiomInputs.OS0Regularity =
      OS0Regularity inputs
  ; PinnedOS.PinnedCMP119OSAxiomInputs.OS1EuclideanCovariance =
      λ G →
        ∀ action observable →
        Limit.limitExpectation (family inputs G)
          (euclideanAct inputs action observable)
        ≡
        Limit.limitExpectation (family inputs G) observable
  ; PinnedOS.PinnedCMP119OSAxiomInputs.OS3PermutationSymmetry =
      OS3PermutationSymmetry inputs
  ; PinnedOS.PinnedCMP119OSAxiomInputs.OS4Clustering =
      OS4Clustering inputs
  ; PinnedOS.PinnedCMP119OSAxiomInputs.OS5GrowthControl =
      OS5GrowthControl inputs
  ; PinnedOS.PinnedCMP119OSAxiomInputs.os0 =
      os0 inputs
  ; PinnedOS.PinnedCMP119OSAxiomInputs.os1 =
      continuumEuclideanInvariant inputs
  ; PinnedOS.PinnedCMP119OSAxiomInputs.os3 =
      os3 inputs
  ; PinnedOS.PinnedCMP119OSAxiomInputs.os4 =
      os4 inputs
  ; PinnedOS.PinnedCMP119OSAxiomInputs.os5 =
      os5 inputs
  }

pinnedConcreteOS1LimitCompilerLevel : ProofLevel
pinnedConcreteOS1LimitCompilerLevel = machineChecked

pinnedConcreteOS1SystemAdapterLevel : ProofLevel
pinnedConcreteOS1SystemAdapterLevel = machineChecked

-- A/OS1 now asks only for finite invariance of the literal normalized CMP119
-- expectation under the selected Euclidean action.  The continuum passage is
-- no longer a separate physical theorem.
literalFiniteCMP119EuclideanInvarianceLevel : ProofLevel
literalFiniteCMP119EuclideanInvarianceLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
