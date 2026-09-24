{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ContinuumFromOSRound432Exact where

------------------------------------------------------------------------
-- A / ROUND432: SAME OS SYSTEM -> CANONICAL CONTINUUM/HILBERT/HAMILTONIAN
--
-- Remove independent Hilbert/Hamiltonian selection from PinnedCMP119ContinuumInputs.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsContinuumSchwingerFromMeasureExact as Schwinger
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as OSR
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ContinuumConstructionExact as Continuum
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record PinnedCMP119ContinuumSemanticInputs
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    {S :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Nat Configuration ℝ
          (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          Hilbert Hamiltonian Vector)}
    (osInputs :
      OSSystem.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vector
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (reconstruction :
      OSR.PinnedCMP119OSReconstruction
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs)
    : Set₂ where
  field
    finiteVolumeCutoffMeasure : ∀ group cutoff →
      Top.IsFiniteVolumeCutoffMeasure S group cutoff
        (Limit.finiteMeasure (OSSystem.family osInputs group) cutoff)

    reflectionPositiveRegularization : ∀ group cutoff →
      Top.IsReflectionPositiveRegularization S group cutoff
        (Limit.finiteMeasure (OSSystem.family osInputs group) cutoff)

    ultravioletYangMillsNormalization : ∀ group →
      Top.HasUltravioletYangMillsNormalization S group
        (Limit.finiteMeasure (OSSystem.family osInputs group))

    asymptoticallyFreeScaleTrajectory : ∀ group →
      Top.HasAsymptoticallyFreeScaleTrajectory S group
        (Limit.finiteMeasure (OSSystem.family osInputs group))

    gaugeSymmetryPreserved : ∀ group →
      Top.GaugeSymmetryPreservedAlongConstruction S group
    localityPreserved : ∀ group →
      Top.LocalityPreservedAlongConstruction S group
    euclideanCovariancePreserved : ∀ group →
      Top.EuclideanCovariancePreservedAlongConstruction S group
    reflectionPositivityPreserved : ∀ group →
      Top.ReflectionPositivityPreservedAlongConstruction S group
    positivityNormalizationPreserved : ∀ group →
      Top.PositivityNormalizationPreservedAlongConstruction S group
    volumeCutoffCompatibility : ∀ group →
      Top.VolumeCutoffCompatibilityPreserved S group

    continuumLimit : ∀ group →
      Top.IsContinuumLimitOf S group
        (Limit.finiteMeasure (OSSystem.family osInputs group))
        (Limit.continuumMeasure (OSSystem.family osInputs group))

    schwingerBelongsToContinuumMeasure : ∀ group →
      Top.SchwingerBelongsToMeasure S
        (Limit.continuumMeasure (OSSystem.family osInputs group))
        (Schwinger.schwingerFromMeasure
          (OSSystem.cylinderEncoding osInputs)
          (Limit.continuumMeasure (OSSystem.family osInputs group)))

    -- Pure semantic interpretation bridges for the already-complete OS system
    -- and already-reconstructed canonical objects.
    acceptedWightmanOrOSAxioms : ∀ group →
      Top.SatisfiesAcceptedWightmanOrOSAxioms S group
        (Schwinger.schwingerFromMeasure
          (OSSystem.cylinderEncoding osInputs)
          (Limit.continuumMeasure (OSSystem.family osInputs group)))

    reconstructedHilbertSpace : ∀ group →
      Top.IsReconstructedHilbertSpace S group
        (Schwinger.schwingerFromMeasure
          (OSSystem.cylinderEncoding osInputs)
          (Limit.continuumMeasure (OSSystem.family osInputs group)))
        (OSR.reconstructedHilbert reconstruction group)

    positiveSelfAdjointHamiltonian : ∀ group →
      Top.IsPositiveSelfAdjointHamiltonian S
        (OSR.reconstructedHilbert reconstruction group)
        (OSR.reconstructedHamiltonian reconstruction group)

open PinnedCMP119ContinuumSemanticInputs public

asPinnedCMP119ContinuumInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      sequenceLimit limitLaws quotient division S osInputs reconstruction} →
  PinnedCMP119ContinuumSemanticInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S} osInputs reconstruction →
  Continuum.PinnedCMP119ContinuumInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vector
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S
asPinnedCMP119ContinuumInputs
    {osInputs = osInputs} {reconstruction = reconstruction} dataSet = record
  { Continuum.PinnedCMP119ContinuumInputs.family =
      OSSystem.family osInputs
  ; Continuum.PinnedCMP119ContinuumInputs.cylinderEncoding =
      OSSystem.cylinderEncoding osInputs
  ; Continuum.PinnedCMP119ContinuumInputs.finiteVolumeCutoffMeasure =
      finiteVolumeCutoffMeasure dataSet
  ; Continuum.PinnedCMP119ContinuumInputs.reflectionPositiveRegularization =
      reflectionPositiveRegularization dataSet
  ; Continuum.PinnedCMP119ContinuumInputs.ultravioletYangMillsNormalization =
      ultravioletYangMillsNormalization dataSet
  ; Continuum.PinnedCMP119ContinuumInputs.asymptoticallyFreeScaleTrajectory =
      asymptoticallyFreeScaleTrajectory dataSet
  ; Continuum.PinnedCMP119ContinuumInputs.gaugeSymmetryPreserved =
      gaugeSymmetryPreserved dataSet
  ; Continuum.PinnedCMP119ContinuumInputs.localityPreserved =
      localityPreserved dataSet
  ; Continuum.PinnedCMP119ContinuumInputs.euclideanCovariancePreserved =
      euclideanCovariancePreserved dataSet
  ; Continuum.PinnedCMP119ContinuumInputs.reflectionPositivityPreserved =
      reflectionPositivityPreserved dataSet
  ; Continuum.PinnedCMP119ContinuumInputs.positivityNormalizationPreserved =
      positivityNormalizationPreserved dataSet
  ; Continuum.PinnedCMP119ContinuumInputs.volumeCutoffCompatibility =
      volumeCutoffCompatibility dataSet
  ; Continuum.PinnedCMP119ContinuumInputs.continuumLimit =
      continuumLimit dataSet
  ; Continuum.PinnedCMP119ContinuumInputs.schwingerBelongsToContinuumMeasure =
      schwingerBelongsToContinuumMeasure dataSet
  ; Continuum.PinnedCMP119ContinuumInputs.acceptedWightmanOrOSAxioms =
      acceptedWightmanOrOSAxioms dataSet
  ; Continuum.PinnedCMP119ContinuumInputs.hilbertSpace =
      OSR.reconstructedHilbert reconstruction
  ; Continuum.PinnedCMP119ContinuumInputs.hamiltonian =
      OSR.reconstructedHamiltonian reconstruction
  ; Continuum.PinnedCMP119ContinuumInputs.reconstructedHilbertSpace =
      reconstructedHilbertSpace dataSet
  ; Continuum.PinnedCMP119ContinuumInputs.positiveSelfAdjointHamiltonian =
      positiveSelfAdjointHamiltonian dataSet
  }

round432CanonicalOSObjectsCompilerLevel : ProofLevel
round432CanonicalOSObjectsCompilerLevel = machineChecked

-- No independent Hilbert-space/Hamiltonian construction remains.
-- The remaining semantic fields are interpretations of already-constructed
-- objects in the top-level Clay semantics.
literalRound432SemanticInterpretationLevel : ProofLevel
literalRound432SemanticInterpretationLevel = conditional
