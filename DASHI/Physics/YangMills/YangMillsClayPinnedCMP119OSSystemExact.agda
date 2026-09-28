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

------------------------------------------------------------------------
-- PRE-GAP PINNED CMP119 OS CORE.
--
-- Same finite family, same cylinder encoding, same OS2 compiler, but no OS4.
------------------------------------------------------------------------

record PinnedCMP119OSCoreInputs
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
    familyCore : ∀ G →
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division

    cylinderEncodingCore :
      Schwinger.CylinderSchwingerEncoding
        (Configuration → ℝ) Position

    observableAlgebraCore :
      OS2.CylinderOSAlgebra (Configuration → ℝ)

    finiteReflectionPositiveCore :
      ∀ G cutoff
        (testFamily :
          Gram.PhysicalOSFiniteTestFamily (Configuration → ℝ) ℝ) →
      0ℝ ≤ℝ
        Gram.physicalReflectedGramQuadraticForm
          (OS2.operations observableAlgebraCore)
          (λ observable →
            Limit.finiteExpectation (familyCore G) cutoff observable)
          testFamily

    OS0RegularityCore : CompactSimpleGroup → Set
    OS1EuclideanCovarianceCore : CompactSimpleGroup → Set
    OS3PermutationSymmetryCore : CompactSimpleGroup → Set
    OS5GrowthControlCore : CompactSimpleGroup → Set

    os0Core : ∀ G → OS0RegularityCore G
    os1Core : ∀ G → OS1EuclideanCovarianceCore G
    os3Core : ∀ G → OS3PermutationSymmetryCore G
    os5Core : ∀ G → OS5GrowthControlCore G

open PinnedCMP119OSCoreInputs public

finiteOS2CoreInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S}
    (inputs :
      PinnedCMP119OSCoreInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  FiniteOS2.FinitePhysicalMeasureContinuumOS2Inputs
    Configuration limitLaws quotient division
finiteOS2CoreInputs inputs group = record
  { FiniteOS2.FinitePhysicalMeasureContinuumOS2Inputs.family =
      familyCore inputs group
  ; FiniteOS2.FinitePhysicalMeasureContinuumOS2Inputs.observableAlgebra =
      observableAlgebraCore inputs
  ; FiniteOS2.FinitePhysicalMeasureContinuumOS2Inputs.finiteReflectionPositive =
      finiteReflectionPositiveCore inputs group
  }

continuumOS2Core :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S}
    (inputs :
      PinnedCMP119OSCoreInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  GramOS.GramReflectionPositive
    (OS2.asOSGramLimitData
      (FiniteOS2.asCylinderOSInputs
        (finiteOS2CoreInputs inputs group)))
    (Limit.limitExpectation (familyCore inputs group))
continuumOS2Core inputs group =
  FiniteOS2.continuumReflectionPositive
    (finiteOS2CoreInputs inputs group)

constructedMeasureCore :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S} →
  PinnedCMP119OSCoreInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S →
  G → Physical.PhysicalContinuumYMMeasure (Configuration → ℝ) ℝ
constructedMeasureCore inputs group =
  Limit.continuumMeasure (familyCore inputs group)

constructedSchwingerCore :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S} →
  PinnedCMP119OSCoreInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S →
  G → Physical.PhysicalSchwingerFamily (Configuration → ℝ) Position ℝ
constructedSchwingerCore inputs group =
  Schwinger.schwingerFromMeasure
    (cylinderEncodingCore inputs)
    (constructedMeasureCore inputs group)

continuumOSCoreSystem :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S}
    (inputs :
      PinnedCMP119OSCoreInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (group : G) →
  OSGap.PreGapContinuumSchwingerSystem
    (Configuration → ℝ) Position ℝ
continuumOSCoreSystem inputs group = record
  { OSGap.PreGapContinuumSchwingerSystem.schwingerCore =
      Physical.schwinger (constructedSchwingerCore inputs group)
  ; OSGap.PreGapContinuumSchwingerSystem.OS0RegularityCore =
      OS0RegularityCore inputs group
  ; OSGap.PreGapContinuumSchwingerSystem.OS1EuclideanCovarianceCore =
      OS1EuclideanCovarianceCore inputs group
  ; OSGap.PreGapContinuumSchwingerSystem.OS2ReflectionPositivityCore =
      GramOS.GramReflectionPositive
        (OS2.asOSGramLimitData
          (FiniteOS2.asCylinderOSInputs
            (finiteOS2CoreInputs inputs group)))
        (Limit.limitExpectation (familyCore inputs group))
  ; OSGap.PreGapContinuumSchwingerSystem.OS3PermutationSymmetryCore =
      OS3PermutationSymmetryCore inputs group
  ; OSGap.PreGapContinuumSchwingerSystem.OS5GrowthControlCore =
      OS5GrowthControlCore inputs group
  ; OSGap.PreGapContinuumSchwingerSystem.os0Core =
      os0Core inputs group
  ; OSGap.PreGapContinuumSchwingerSystem.os1Core =
      os1Core inputs group
  ; OSGap.PreGapContinuumSchwingerSystem.os2Core =
      continuumOS2Core inputs group
  ; OSGap.PreGapContinuumSchwingerSystem.os3Core =
      os3Core inputs group
  ; OSGap.PreGapContinuumSchwingerSystem.os5Core =
      os5Core inputs group
  }

record CMP119OS4Attachment
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState : Set}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    {S}
    (core :
      PinnedCMP119OSCoreInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S) : Set₂ where
  field
    OS4ClusteringAttached : G → Set
    os4Attached : ∀ group → OS4ClusteringAttached group

open CMP119OS4Attachment public

corePlusOS4Inputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S}
    (core :
      PinnedCMP119OSCoreInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S) →
  CMP119OS4Attachment core →
  PinnedCMP119OSAxiomInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S
corePlusOS4Inputs core clustering = record
  { PinnedCMP119OSAxiomInputs.family =
      familyCore core
  ; PinnedCMP119OSAxiomInputs.cylinderEncoding =
      cylinderEncodingCore core
  ; PinnedCMP119OSAxiomInputs.observableAlgebra =
      observableAlgebraCore core
  ; PinnedCMP119OSAxiomInputs.finiteReflectionPositive =
      finiteReflectionPositiveCore core
  ; PinnedCMP119OSAxiomInputs.OS0Regularity =
      OS0RegularityCore core
  ; PinnedCMP119OSAxiomInputs.OS1EuclideanCovariance =
      OS1EuclideanCovarianceCore core
  ; PinnedCMP119OSAxiomInputs.OS3PermutationSymmetry =
      OS3PermutationSymmetryCore core
  ; PinnedCMP119OSAxiomInputs.OS4Clustering =
      OS4ClusteringAttached clustering
  ; PinnedCMP119OSAxiomInputs.OS5GrowthControl =
      OS5GrowthControlCore core
  ; PinnedCMP119OSAxiomInputs.os0 =
      os0Core core
  ; PinnedCMP119OSAxiomInputs.os1 =
      os1Core core
  ; PinnedCMP119OSAxiomInputs.os3 =
      os3Core core
  ; PinnedCMP119OSAxiomInputs.os4 =
      os4Attached clustering
  ; PinnedCMP119OSAxiomInputs.os5 =
      os5Core core
  }

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

pinnedCMP119PreGapOSCoreCompilerLevel : ProofLevel
pinnedCMP119PreGapOSCoreCompilerLevel = machineChecked

pinnedCMP119OS4AttachmentCompilerLevel : ProofLevel
pinnedCMP119OS4AttachmentCompilerLevel = machineChecked

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
