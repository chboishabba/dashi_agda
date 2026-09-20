{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact where

------------------------------------------------------------------------
-- SAME CMP119 LIMIT -> CONCRETE CONTINUUM OS SYSTEM
--
-- The measure and Schwinger family are constructed from the normalized finite
-- physical family.  OS2 is not an input: it is compiled from finite Wilson
-- reflection positivity on those exact finite normalized expectations.
--
-- OS0/OS1/OS3/OS4/OS5 remain the genuine continuum analytic inputs.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsContinuumSchwingerFromMeasureExact as Schwinger
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureContinuumOS2Exact as FiniteOS2
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact as GramOS
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record PinnedCMP119OSAxiomInputs
    (CompactSimpleGroup Spacetime Configuration Position
     CurvaturePolynomial LocalOperator OPECoefficient StressTensor
     HilbertSpace Hamiltonian VacuumState : Set)
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

    -- Remaining OS axioms on the SAME constructed Schwinger family.
    OS0Regularity : CompactSimpleGroup → Set
    OS1EuclideanCovariance : CompactSimpleGroup → Set
    OS3PermutationSymmetry : CompactSimpleGroup → Set
    OS4Clustering : CompactSimpleGroup → Set
    OS5GrowthControl : CompactSimpleGroup → Set

    os0 : ∀ G → OS0Regularity G
    os1 : ∀ G → OS1EuclideanCovariance G
    os3 : ∀ G → OS3PermutationSymmetry G
    os4 : ∀ G → OS4Clustering G
    os5 : ∀ G → OS5GrowthControl G

open PinnedCMP119OSAxiomInputs public

finiteOS2Inputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S}
    (inputs :
      PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  FiniteOS2.FinitePhysicalMeasureContinuumOS2Inputs
    Configuration limitLaws quotient division
finiteOS2Inputs inputs group = record
  { FiniteOS2.FinitePhysicalMeasureContinuumOS2Inputs.family =
      family inputs group
  ; FiniteOS2.FinitePhysicalMeasureContinuumOS2Inputs.observableAlgebra =
      observableAlgebra inputs
  ; FiniteOS2.FinitePhysicalMeasureContinuumOS2Inputs.finiteReflectionPositive =
      finiteReflectionPositive inputs group
  }

continuumOS2 :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S}
    (inputs :
      PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  GramOS.GramReflectionPositive
    (OS2.asOSGramLimitData
      (FiniteOS2.asCylinderOSInputs
        (finiteOS2Inputs inputs group)))
    (Limit.limitExpectation (family inputs group))
continuumOS2 inputs group =
  FiniteOS2.continuumReflectionPositive
    (finiteOS2Inputs inputs group)

constructedMeasure :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S} →
  PinnedCMP119OSAxiomInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S →
  G → Physical.PhysicalContinuumYMMeasure (Configuration → ℝ) ℝ
constructedMeasure inputs group =
  Limit.continuumMeasure (family inputs group)

constructedSchwinger :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S} →
  PinnedCMP119OSAxiomInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S →
  G → Physical.PhysicalSchwingerFamily (Configuration → ℝ) Position ℝ
constructedSchwinger inputs group =
  Schwinger.schwingerFromMeasure
    (cylinderEncoding inputs)
    (constructedMeasure inputs group)

continuumOSSystem :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S}
    (inputs :
      PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (group : G) →
  OSGap.ContinuumSchwingerSystem
    (Configuration → ℝ) Position ℝ
continuumOSSystem inputs group = record
  { OSGap.ContinuumSchwingerSystem.schwinger =
      Physical.schwinger (constructedSchwinger inputs group)
  ; OSGap.ContinuumSchwingerSystem.OS0Regularity =
      OS0Regularity inputs group
  ; OSGap.ContinuumSchwingerSystem.OS1EuclideanCovariance =
      OS1EuclideanCovariance inputs group
  ; OSGap.ContinuumSchwingerSystem.OS2ReflectionPositivity =
      GramOS.GramReflectionPositive
        (OS2.asOSGramLimitData
          (FiniteOS2.asCylinderOSInputs
            (finiteOS2Inputs inputs group)))
        (Limit.limitExpectation (family inputs group))
  ; OSGap.ContinuumSchwingerSystem.OS3PermutationSymmetry =
      OS3PermutationSymmetry inputs group
  ; OSGap.ContinuumSchwingerSystem.OS4Clustering =
      OS4Clustering inputs group
  ; OSGap.ContinuumSchwingerSystem.OS5GrowthControl =
      OS5GrowthControl inputs group
  ; OSGap.ContinuumSchwingerSystem.os0 =
      os0 inputs group
  ; OSGap.ContinuumSchwingerSystem.os1 =
      os1 inputs group
  ; OSGap.ContinuumSchwingerSystem.os2 =
      continuumOS2 inputs group
  ; OSGap.ContinuumSchwingerSystem.os3 =
      os3 inputs group
  ; OSGap.ContinuumSchwingerSystem.os4 =
      os4 inputs group
  ; OSGap.ContinuumSchwingerSystem.os5 =
      os5 inputs group
  }

pinnedCMP119OS2CompilerLevel : ProofLevel
pinnedCMP119OS2CompilerLevel = machineChecked

pinnedCMP119SameMeasureSchwingerCompilerLevel : ProofLevel
pinnedCMP119SameMeasureSchwingerCompilerLevel = machineChecked

pinnedCMP119OSSystemCompilerLevel : ProofLevel
pinnedCMP119OSSystemCompilerLevel = machineChecked

-- Genuine continuum inputs remaining at this stage.
pinnedCMP119OS0Level : ProofLevel
pinnedCMP119OS0Level = conditional

pinnedCMP119OS1Level : ProofLevel
pinnedCMP119OS1Level = conditional

pinnedCMP119OS3Level : ProofLevel
pinnedCMP119OS3Level = conditional

pinnedCMP119OS4Level : ProofLevel
pinnedCMP119OS4Level = conditional

pinnedCMP119OS5Level : ProofLevel
pinnedCMP119OS5Level = conditional

literalFiniteWilsonReflectionPositivityLevel : ProofLevel
literalFiniteWilsonReflectionPositivityLevel = conditional
