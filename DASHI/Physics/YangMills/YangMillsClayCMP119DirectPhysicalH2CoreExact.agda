{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCMP119DirectPhysicalH2CoreExact where

------------------------------------------------------------------------
-- H2 CORE ON THE ACTUAL CMP119 FAMILY, WITH OS4 REMOVED.
--
-- Physical dependency:
--
--   R582 finite/source core
--      -> pinned OS0/1/2/3/5 core
--      -> pre-gap OS reconstruction
--
-- H1 supplies OS4 later on this exact Schwinger family.  Only then do we
-- compile the historical clustered H2 record for legacy downstream consumers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayPublishedFiniteOSCoreMomentSourceRound582Exact as R582
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as OSR
import DASHI.Physics.YangMills.YangMillsClayCMP119DirectPhysicalH2Exact as LegacyH2
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record CMP119DirectPhysicalH2Core
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
     EuclideanAction Permutation Epsilon Witness : Set)
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
          Hilbert Hamiltonian Vector))
    : Set₂ where
  field
    finiteCoreSource :
      R582.PublishedFiniteOSCoreMomentSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vector
        EuclideanAction Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S

  coreInputs :
    OSSystem.PinnedCMP119OSCoreInputs
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vector
      {sequenceLimit = sequenceLimit}
      limitLaws quotient division S
  coreInputs =
    R582.asPinnedOSCoreInputs finiteCoreSource

  field
    reconstructionCore :
      OSR.PinnedCMP119PreGapOSReconstruction
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = S}
        coreInputs

    --------------------------------------------------------------------
    -- Literal finite-family semantics do not require OS4.
    --------------------------------------------------------------------
    finiteVolumeCutoffMeasureCore : ∀ group cutoff →
      Top.IsFiniteVolumeCutoffMeasure S group cutoff
        (Limit.finiteMeasure (OSSystem.familyCore coreInputs group) cutoff)

    reflectionPositiveRegularizationCore : ∀ group cutoff →
      Top.IsReflectionPositiveRegularization S group cutoff
        (Limit.finiteMeasure (OSSystem.familyCore coreInputs group) cutoff)

    ultravioletYangMillsNormalizationCore : ∀ group →
      Top.HasUltravioletYangMillsNormalization S group
        (Limit.finiteMeasure (OSSystem.familyCore coreInputs group))

    asymptoticallyFreeScaleTrajectoryCore : ∀ group →
      Top.HasAsymptoticallyFreeScaleTrajectory S group
        (Limit.finiteMeasure (OSSystem.familyCore coreInputs group))

    gaugeSymmetryPreservedCore : ∀ group →
      Top.GaugeSymmetryPreservedAlongConstruction S group

    localityPreservedCore : ∀ group →
      Top.LocalityPreservedAlongConstruction S group

    euclideanCovariancePreservedCore : ∀ group →
      Top.EuclideanCovariancePreservedAlongConstruction S group

    reflectionPositivityPreservedCore : ∀ group →
      Top.ReflectionPositivityPreservedAlongConstruction S group

    positivityNormalizationPreservedCore : ∀ group →
      Top.PositivityNormalizationPreserved S group

    volumeCutoffCompatibilityCore : ∀ group →
      Top.VolumeCutoffCompatibilityPreserved S group

    --------------------------------------------------------------------
    -- H2 continuum/reconstruction semantics before clustering.
    --------------------------------------------------------------------
    continuumLimitCore : ∀ group →
      Top.IsContinuumLimitOf S group
        (Limit.finiteMeasure (OSSystem.familyCore coreInputs group))
        (OSSystem.constructedMeasureCore coreInputs group)

    schwingerBelongsToContinuumMeasureCore : ∀ group →
      Top.SchwingerBelongsToMeasure S
        (OSSystem.constructedMeasureCore coreInputs group)
        (OSSystem.constructedSchwingerCore coreInputs group)

    reconstructedHilbertSpaceMeaningCore : ∀ group →
      Top.IsReconstructedHilbertSpace S group
        (OSSystem.constructedSchwingerCore coreInputs group)
        (OSR.reconstructedHilbertCore reconstructionCore group)

    positiveSelfAdjointHamiltonianMeaningCore : ∀ group →
      Top.IsPositiveSelfAdjointHamiltonian S
        (OSR.reconstructedHilbertCore reconstructionCore group)
        (OSR.reconstructedHamiltonianCore reconstructionCore group)

open CMP119DirectPhysicalH2Core public

record CMP119DirectPhysicalH2OS4Attachment
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
     EuclideanAction Permutation Epsilon Witness : Set}
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
      CMP119DirectPhysicalH2Core
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    : Set₂ where
  field
    OS4Clustering : G → Set
    os4 : ∀ group → OS4Clustering group

    -- The final human OS interpretation is paid only after H1 attaches
    -- clustering to this exact core Schwinger family.
    acceptedWightmanOrOSAxioms : ∀ group →
      Top.SatisfiesAcceptedWightmanOrOSAxioms S group
        (OSSystem.constructedSchwingerCore (coreInputs core) group)

open CMP119DirectPhysicalH2OS4Attachment public

asR582OS4Attachment :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      sequenceLimit limitLaws quotient division S}
    {core :
      CMP119DirectPhysicalH2Core
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S} →
  CMP119DirectPhysicalH2OS4Attachment core →
  R582.CoreOS4Attachment (finiteCoreSource core)
asR582OS4Attachment clustering = record
  { R582.CoreOS4Attachment.OS4Clustering =
      OS4Clustering clustering
  ; R582.CoreOS4Attachment.os4 =
      os4 clustering
  }

asPinnedOS4Attachment :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      sequenceLimit limitLaws quotient division S}
    {core :
      CMP119DirectPhysicalH2Core
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S} →
  CMP119DirectPhysicalH2OS4Attachment core →
  OSSystem.CMP119OS4Attachment (coreInputs core)
asPinnedOS4Attachment clustering = record
  { OSSystem.CMP119OS4Attachment.OS4ClusteringAttached =
      OS4Clustering clustering
  ; OSSystem.CMP119OS4Attachment.os4Attached =
      os4 clustering
  }

asLegacyH2 :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      sequenceLimit limitLaws quotient division S}
    (core :
      CMP119DirectPhysicalH2Core
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S) →
  CMP119DirectPhysicalH2OS4Attachment core →
  LegacyH2.CMP119DirectPhysicalH2
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    EuclideanAction Permutation Epsilon Witness
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S
asLegacyH2 core clustering = record
  { LegacyH2.CMP119DirectPhysicalH2.finiteOSSource =
      R582.corePlusOS4ToR581
        (finiteCoreSource core)
        (asR582OS4Attachment clustering)
  ; LegacyH2.CMP119DirectPhysicalH2.reconstruction =
      OSR.preGapPlusOS4ToLegacyReconstruction
        (reconstructionCore core)
        (asPinnedOS4Attachment clustering)
  ; LegacyH2.CMP119DirectPhysicalH2.finiteVolumeCutoffMeasure =
      finiteVolumeCutoffMeasureCore core
  ; LegacyH2.CMP119DirectPhysicalH2.reflectionPositiveRegularization =
      reflectionPositiveRegularizationCore core
  ; LegacyH2.CMP119DirectPhysicalH2.ultravioletYangMillsNormalization =
      ultravioletYangMillsNormalizationCore core
  ; LegacyH2.CMP119DirectPhysicalH2.asymptoticallyFreeScaleTrajectory =
      asymptoticallyFreeScaleTrajectoryCore core
  ; LegacyH2.CMP119DirectPhysicalH2.gaugeSymmetryPreserved =
      gaugeSymmetryPreservedCore core
  ; LegacyH2.CMP119DirectPhysicalH2.localityPreserved =
      localityPreservedCore core
  ; LegacyH2.CMP119DirectPhysicalH2.euclideanCovariancePreserved =
      euclideanCovariancePreservedCore core
  ; LegacyH2.CMP119DirectPhysicalH2.reflectionPositivityPreserved =
      reflectionPositivityPreservedCore core
  ; LegacyH2.CMP119DirectPhysicalH2.positivityNormalizationPreserved =
      positivityNormalizationPreservedCore core
  ; LegacyH2.CMP119DirectPhysicalH2.volumeCutoffCompatibility =
      volumeCutoffCompatibilityCore core
  ; LegacyH2.CMP119DirectPhysicalH2.continuumLimit =
      continuumLimitCore core
  ; LegacyH2.CMP119DirectPhysicalH2.schwingerBelongsToContinuumMeasure =
      schwingerBelongsToContinuumMeasureCore core
  ; LegacyH2.CMP119DirectPhysicalH2.acceptedWightmanOrOSAxioms =
      acceptedWightmanOrOSAxioms clustering
  ; LegacyH2.CMP119DirectPhysicalH2.reconstructedHilbertSpaceMeaning =
      reconstructedHilbertSpaceMeaningCore core
  ; LegacyH2.CMP119DirectPhysicalH2.positiveSelfAdjointHamiltonianMeaning =
      positiveSelfAdjointHamiltonianMeaningCore core
  }

cmp119H2CoreObjectConstructionLevel : ProofLevel
cmp119H2CoreObjectConstructionLevel = machineChecked

cmp119H2CoreToLegacyAfterOS4CompilerLevel : ProofLevel
cmp119H2CoreToLegacyAfterOS4CompilerLevel = machineChecked

os4RequiredToConstructH2Core : Bool
os4RequiredToConstructH2Core = false

os4RequiredToConstructH2CoreIsFalse :
  os4RequiredToConstructH2Core ≡ false
os4RequiredToConstructH2CoreIsFalse = refl

cmp119H2CorePhysicalInstantiationLevel : ProofLevel
cmp119H2CorePhysicalInstantiationLevel =
  R582.literalRound582PublishedFiniteOSCoreMomentSourceLevel

cmp119H2OS4AttachmentLevel : ProofLevel
cmp119H2OS4AttachmentLevel = conditional
