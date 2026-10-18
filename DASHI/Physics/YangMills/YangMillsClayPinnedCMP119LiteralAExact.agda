{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119LiteralAExact where

------------------------------------------------------------------------
-- LITERAL A ON ONE CMP119 -> OS RECONSTRUCTION OBJECT
--
-- Construct the literal pinned finite/continuum objects from one source family:
--
--   CMP119 finite measures
--      -> normalized expectation limit
--      -> continuum measure
--      -> same-measure Schwinger family
--      -> OS0..OS5 (OS2 compiled from finite Wilson RP)
--      -> OS reconstruction
--      -> SAME Hilbert space and Hamiltonian.
--
-- Only semantic/physical theorem predicates on these fixed objects remain.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as OSR
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record PinnedCMP119LiteralAInputs
    (CompactSimpleGroup Spacetime Configuration Position
     CurvaturePolynomial LocalOperator OPECoefficient StressTensor
     HilbertSpace Vector Hamiltonian Algebra : Set)
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
    (osInputs :
      OSSystem.PinnedCMP119OSAxiomInputs
        CompactSimpleGroup Spacetime Configuration Position
        CurvaturePolynomial LocalOperator OPECoefficient StressTensor
        HilbertSpace Hamiltonian Vector
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (reconstruction :
      OSR.PinnedCMP119OSReconstruction
        CompactSimpleGroup Spacetime Configuration Position
        CurvaturePolynomial LocalOperator OPECoefficient StressTensor
        HilbertSpace Vector Hamiltonian Algebra
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs) : Set₂ where
  field
    -- Literal finite-family semantics on the exact CMP119 family.
    finiteVolumeCutoffMeasure : ∀ G cutoff →
      Top.IsFiniteVolumeCutoffMeasure S G cutoff
        (Limit.finiteMeasure (OSSystem.family osInputs G) cutoff)

    reflectionPositiveRegularization : ∀ G cutoff →
      Top.IsReflectionPositiveRegularization S G cutoff
        (Limit.finiteMeasure (OSSystem.family osInputs G) cutoff)

    ultravioletYangMillsNormalization : ∀ G →
      Top.HasUltravioletYangMillsNormalization S G
        (Limit.finiteMeasure (OSSystem.family osInputs G))

    asymptoticallyFreeScaleTrajectory : ∀ G →
      Top.HasAsymptoticallyFreeScaleTrajectory S G
        (Limit.finiteMeasure (OSSystem.family osInputs G))

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

    -- Continuum semantics on the constructed objects.
    continuumLimit : ∀ G →
      Top.IsContinuumLimitOf S G
        (Limit.finiteMeasure (OSSystem.family osInputs G))
        (OSSystem.constructedMeasure osInputs G)

    schwingerBelongsToContinuumMeasure : ∀ G →
      Top.SchwingerBelongsToMeasure S
        (OSSystem.constructedMeasure osInputs G)
        (OSSystem.constructedSchwinger osInputs G)

    acceptedWightmanOrOSAxioms : ∀ G →
      Top.SatisfiesAcceptedWightmanOrOSAxioms S G
        (OSSystem.constructedSchwinger osInputs G)

    reconstructedHilbertSpaceMeaning : ∀ G →
      Top.IsReconstructedHilbertSpace S G
        (OSSystem.constructedSchwinger osInputs G)
        (OSR.reconstructedHilbert reconstruction G)

    positiveSelfAdjointHamiltonianMeaning : ∀ G →
      Top.IsPositiveSelfAdjointHamiltonian S
        (OSR.reconstructedHilbert reconstruction G)
        (OSR.reconstructedHamiltonian reconstruction G)

open PinnedCMP119LiteralAInputs public

compilePinnedFinite :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      sequenceLimit limitLaws quotient division S osInputs reconstruction} →
  PinnedCMP119LiteralAInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S} osInputs reconstruction →
  Pinned.PinnedFiniteYMConstruction S
compilePinnedFinite {osInputs = osInputs} inputs = record
  { Pinned.PinnedFiniteYMConstruction.finiteMeasure =
      λ G cutoff →
        Limit.finiteMeasure
          (OSSystem.family osInputs G)
          cutoff
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
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      sequenceLimit limitLaws quotient division S osInputs reconstruction}
    (inputs :
      PinnedCMP119LiteralAInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction) →
  Pinned.PinnedContinuumYMConstruction S
    (compilePinnedFinite inputs)
compilePinnedContinuum
    {osInputs = osInputs} {reconstruction = reconstruction}
    inputs = record
  { Pinned.PinnedContinuumYMConstruction.continuumMeasure =
      OSSystem.constructedMeasure osInputs
  ; Pinned.PinnedContinuumYMConstruction.schwinger =
      OSSystem.constructedSchwinger osInputs
  ; Pinned.PinnedContinuumYMConstruction.hilbertSpace =
      OSR.reconstructedHilbert reconstruction
  ; Pinned.PinnedContinuumYMConstruction.hamiltonian =
      OSR.reconstructedHamiltonian reconstruction
  ; Pinned.PinnedContinuumYMConstruction.continuumLimit =
      continuumLimit inputs
  ; Pinned.PinnedContinuumYMConstruction.schwingerBelongsToContinuumMeasure =
      schwingerBelongsToContinuumMeasure inputs
  ; Pinned.PinnedContinuumYMConstruction.acceptedWightmanOrOSAxioms =
      acceptedWightmanOrOSAxioms inputs
  ; Pinned.PinnedContinuumYMConstruction.reconstructedHilbertSpace =
      reconstructedHilbertSpaceMeaning inputs
  ; Pinned.PinnedContinuumYMConstruction.positiveSelfAdjointHamiltonian =
      positiveSelfAdjointHamiltonianMeaning inputs
  }

literalAContinuumMeasureIsConstructedCMP119Limit :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      sequenceLimit limitLaws quotient division S osInputs reconstruction}
    (inputs :
      PinnedCMP119LiteralAInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction)
    group →
  Pinned.continuumMeasure (compilePinnedContinuum inputs) group
  _≡_
  OSSystem.constructedMeasure osInputs group
literalAContinuumMeasureIsConstructedCMP119Limit inputs group =
  refl

literalASchwingerIsSameConstructedMeasure :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      sequenceLimit limitLaws quotient division S osInputs reconstruction}
    (inputs :
      PinnedCMP119LiteralAInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction)
    group →
  Pinned.schwinger (compilePinnedContinuum inputs) group
  _≡_
  OSSystem.constructedSchwinger osInputs group
literalASchwingerIsSameConstructedMeasure inputs group =
  refl

literalAHilbertIsOSReconstructed :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      sequenceLimit limitLaws quotient division S osInputs reconstruction}
    (inputs :
      PinnedCMP119LiteralAInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction)
    group →
  Pinned.hilbertSpace (compilePinnedContinuum inputs) group
  _≡_
  OSR.reconstructedHilbert reconstruction group
literalAHilbertIsOSReconstructed inputs group =
  refl

literalAHamiltonianIsOSReconstructed :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      sequenceLimit limitLaws quotient division S osInputs reconstruction}
    (inputs :
      PinnedCMP119LiteralAInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction)
    group →
  Pinned.hamiltonian (compilePinnedContinuum inputs) group
  _≡_
  OSR.reconstructedHamiltonian reconstruction group
literalAHamiltonianIsOSReconstructed inputs group =
  refl

pinnedCMP119LiteralAFiniteCompilerLevel : ProofLevel
pinnedCMP119LiteralAFiniteCompilerLevel = machineChecked

pinnedCMP119LiteralAContinuumCompilerLevel : ProofLevel
pinnedCMP119LiteralAContinuumCompilerLevel = machineChecked

pinnedCMP119LiteralASameObjectCompilerLevel : ProofLevel
pinnedCMP119LiteralASameObjectCompilerLevel = machineChecked

-- These are now the genuine A theorem predicates; object selection is gone.
literalCMP119ContinuumLimitPhysicalLevel : ProofLevel
literalCMP119ContinuumLimitPhysicalLevel = conditional

literalCMP119OS01345PhysicalLevel : ProofLevel
literalCMP119OS01345PhysicalLevel = conditional

literalCMP119SemanticOSReconstructionAttachmentLevel : ProofLevel
literalCMP119SemanticOSReconstructionAttachmentLevel = conditional
