{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ContinuumConstructionExact where

------------------------------------------------------------------------
-- LITERAL CMP119 FINITE FAMILY -> PINNED CONTINUUM MEASURE + SCHWINGER
--
-- The continuum measure and Schwinger family are CONSTRUCTED, not chosen:
--
--   finite physical normalized expectations
--        -> cutoff limit expectation
--        -> PhysicalContinuumYMMeasure
--        -> cylinder two-point encoding
--        -> PhysicalSchwingerFamily
--
-- Thus the same-object part of literal A is definitional.  Remaining fields are
-- exactly the physical continuum/OS/reconstruction theorems on these objects.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsContinuumSchwingerFromMeasureExact as Schwinger
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record PinnedCMP119ContinuumInputs
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

    -- Literal finite-family semantics.  No finite object is selected again.
    finiteVolumeCutoffMeasure : ∀ G cutoff →
      Top.IsFiniteVolumeCutoffMeasure S G cutoff
        (Limit.finiteMeasure (family G) cutoff)

    reflectionPositiveRegularization : ∀ G cutoff →
      Top.IsReflectionPositiveRegularization S G cutoff
        (Limit.finiteMeasure (family G) cutoff)

    ultravioletYangMillsNormalization : ∀ G →
      Top.HasUltravioletYangMillsNormalization S G
        (Limit.finiteMeasure (family G))

    asymptoticallyFreeScaleTrajectory : ∀ G →
      Top.HasAsymptoticallyFreeScaleTrajectory S G
        (Limit.finiteMeasure (family G))

    gaugeSymmetryPreserved : ∀ G →
      Top.GaugeSymmetryPreservedAlongConstruction S G

    localityPreserved : ∀ G →
      Top.LocalityPreservedAlongConstruction S G

    euclideanCovariancePreserved : ∀ G →
      Top.EuclideanCovariancePreservedAlongConstruction S G

    reflectionPositivityPreserved : ∀ G →
      Top.ReflectionPositivityPreservedAlongConstruction S G

    positivityNormalizationPreserved : ∀ G →
      Top.PositivityNormalizationPreservedAlongConstruction S G

    volumeCutoffCompatibility : ∀ G →
      Top.VolumeCutoffCompatibilityPreserved S G

    -- Genuine continuum analysis on the CONSTRUCTED measure.
    continuumLimit : ∀ G →
      Top.IsContinuumLimitOf S G
        (Limit.finiteMeasure (family G))
        (Limit.continuumMeasure (family G))

    schwingerBelongsToContinuumMeasure : ∀ G →
      Top.SchwingerBelongsToMeasure S
        (Limit.continuumMeasure (family G))
        (Schwinger.schwingerFromMeasure
          cylinderEncoding
          (Limit.continuumMeasure (family G)))

    acceptedWightmanOrOSAxioms : ∀ G →
      Top.SatisfiesAcceptedWightmanOrOSAxioms S G
        (Schwinger.schwingerFromMeasure
          cylinderEncoding
          (Limit.continuumMeasure (family G)))

    hilbertSpace : CompactSimpleGroup → HilbertSpace
    hamiltonian : CompactSimpleGroup → Hamiltonian

    reconstructedHilbertSpace : ∀ G →
      Top.IsReconstructedHilbertSpace S G
        (Schwinger.schwingerFromMeasure
          cylinderEncoding
          (Limit.continuumMeasure (family G)))
        (hilbertSpace G)

    positiveSelfAdjointHamiltonian : ∀ G →
      Top.IsPositiveSelfAdjointHamiltonian S
        (hilbertSpace G)
        (hamiltonian G)

open PinnedCMP119ContinuumInputs public

compilePinnedFinite :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S} →
  PinnedCMP119ContinuumInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S →
  Pinned.PinnedFiniteYMConstruction S
compilePinnedFinite inputs = record
  { Pinned.PinnedFiniteYMConstruction.finiteMeasure =
      λ G cutoff → Limit.finiteMeasure (family inputs G) cutoff
  ; Pinned.PinnedFiniteYMConstruction.finiteVolumeCutoffMeasure =
      finiteVolumeCutoffMeasure inputs
  ; Pinned.PinnedFiniteYMConstruction.reflectionPositiveRegularization =
      reflectionPositiveRegularization inputs
  ; Pinned.PinnedFiniteYMConstruction.ultravioletYangMillsNormalization =
      ultravioletYangMillsNormalization inputs
  ; Pinned.PinnedFiniteYMConstruction.asymptoticallyFreeScaleTrajectory =
      asymptoticallyFreeScaleTrajectory inputs
  ; Pinned.PinnedFiniteYMConstruction.gaugeSymmetryPreserved =
      gaugeSymmetryPreserved inputs
  ; Pinned.PinnedFiniteYMConstruction.localityPreserved =
      localityPreserved inputs
  ; Pinned.PinnedFiniteYMConstruction.euclideanCovariancePreserved =
      euclideanCovariancePreserved inputs
  ; Pinned.PinnedFiniteYMConstruction.reflectionPositivityPreserved =
      reflectionPositivityPreserved inputs
  ; Pinned.PinnedFiniteYMConstruction.positivityNormalizationPreserved =
      positivityNormalizationPreserved inputs
  ; Pinned.PinnedFiniteYMConstruction.volumeCutoffCompatibility =
      volumeCutoffCompatibility inputs
  }

compilePinnedContinuum :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S}
    (inputs :
      PinnedCMP119ContinuumInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S) →
  Pinned.PinnedContinuumYMConstruction S
    (compilePinnedFinite inputs)
compilePinnedContinuum inputs = record
  { Pinned.PinnedContinuumYMConstruction.continuumMeasure =
      λ G → Limit.continuumMeasure (family inputs G)
  ; Pinned.PinnedContinuumYMConstruction.schwinger =
      λ G →
        Schwinger.schwingerFromMeasure
          (cylinderEncoding inputs)
          (Limit.continuumMeasure (family inputs G))
  ; Pinned.PinnedContinuumYMConstruction.hilbertSpace =
      hilbertSpace inputs
  ; Pinned.PinnedContinuumYMConstruction.hamiltonian =
      hamiltonian inputs
  ; Pinned.PinnedContinuumYMConstruction.continuumLimit =
      continuumLimit inputs
  ; Pinned.PinnedContinuumYMConstruction.schwingerBelongsToContinuumMeasure =
      schwingerBelongsToContinuumMeasure inputs
  ; Pinned.PinnedContinuumYMConstruction.acceptedWightmanOrOSAxioms =
      acceptedWightmanOrOSAxioms inputs
  ; Pinned.PinnedContinuumYMConstruction.reconstructedHilbertSpace =
      reconstructedHilbertSpace inputs
  ; Pinned.PinnedContinuumYMConstruction.positiveSelfAdjointHamiltonian =
      positiveSelfAdjointHamiltonian inputs
  }

pinnedContinuumMeasureIsCMP119Limit :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S}
    (inputs :
      PinnedCMP119ContinuumInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  Pinned.continuumMeasure
    (compilePinnedContinuum inputs) group
  _≡_
  Limit.continuumMeasure (family inputs group)
pinnedContinuumMeasureIsCMP119Limit inputs group =
  refl

pinnedSchwingerIsSameMeasureCorrelation :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S}
    (inputs :
      PinnedCMP119ContinuumInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  Pinned.schwinger
    (compilePinnedContinuum inputs) group
  _≡_
  Schwinger.schwingerFromMeasure
    (cylinderEncoding inputs)
    (Limit.continuumMeasure (family inputs group))
pinnedSchwingerIsSameMeasureCorrelation inputs group =
  refl

pinnedCMP119FiniteCompilerLevel : ProofLevel
pinnedCMP119FiniteCompilerLevel = machineChecked

pinnedCMP119ContinuumMeasureCompilerLevel : ProofLevel
pinnedCMP119ContinuumMeasureCompilerLevel = machineChecked

pinnedCMP119SchwingerSameObjectCompilerLevel : ProofLevel
pinnedCMP119SchwingerSameObjectCompilerLevel = machineChecked

-- Remaining A theorem content on these now-fixed objects.
pinnedCMP119ContinuumLimitLevel : ProofLevel
pinnedCMP119ContinuumLimitLevel = conditional

pinnedCMP119FullOSAxiomsAndReconstructionLevel : ProofLevel
pinnedCMP119FullOSAxiomsAndReconstructionLevel = conditional
