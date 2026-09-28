{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCMP119DirectPhysicalH2Exact where

------------------------------------------------------------------------
-- H2 DIRECT PHYSICAL SOURCE ON THE ACTUAL CMP119 FAMILY.
--
-- Object choice is eliminated:
--
--   preferred published finite-OS + literal-moment source (R581)
--     -> exact pinned osInputs
--     -> real continuum measure / Schwinger family
--     -> exact OS0..OS5 system
--     -> one OS reconstruction of THAT system.
--
-- The remaining fields are only literal endpoint interpretations of these
-- already-fixed objects.  No second finite family, continuum measure,
-- Schwinger family, Hilbert space, or Hamiltonian is selected here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayPublishedFiniteOSSourceRound462Exact as R462
import DASHI.Physics.YangMills.YangMillsClayPublishedFiniteOSMomentSourceRound581Exact as R581
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as OSR
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119LiteralAExact as LiteralA
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record CMP119DirectPhysicalH2
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
    --------------------------------------------------------------------
    -- Preferred H2 finite/OS source.
    --
    -- Use the published finite Euclidean/bosonic/Wilson-RP source directly.
    -- Explicit Haar change-of-variables, Peter-Weyl square reconstruction and
    -- projective Prokhorov are stronger audit producers, not H2 prerequisites.
    --------------------------------------------------------------------
    finiteOSSource :
      R581.PublishedFiniteOSMomentSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vector
        EuclideanAction Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S

  osInputs :
    OSSystem.PinnedCMP119OSAxiomInputs
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vector
      {sequenceLimit = sequenceLimit}
      limitLaws quotient division S
  osInputs =
    R462.asPinnedOSAxiomInputs
      (R581.asPublishedFiniteOSSource finiteOSSource)

  field
    reconstruction :
      OSR.PinnedCMP119OSReconstruction
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = S}
        osInputs

    --------------------------------------------------------------------
    -- Literal finite-family semantics on the exact preferred R581/R462 family.
    --------------------------------------------------------------------
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

    --------------------------------------------------------------------
    -- H2 literal semantics on the exact constructed real continuum objects.
    --------------------------------------------------------------------
    continuumLimit : ∀ group →
      Top.IsContinuumLimitOf S group
        (Limit.finiteMeasure (OSSystem.family osInputs group))
        (OSSystem.constructedMeasure osInputs group)

    schwingerBelongsToContinuumMeasure : ∀ group →
      Top.SchwingerBelongsToMeasure S
        (OSSystem.constructedMeasure osInputs group)
        (OSSystem.constructedSchwinger osInputs group)

    acceptedWightmanOrOSAxioms : ∀ group →
      Top.SatisfiesAcceptedWightmanOrOSAxioms S group
        (OSSystem.constructedSchwinger osInputs group)

    reconstructedHilbertSpaceMeaning : ∀ group →
      Top.IsReconstructedHilbertSpace S group
        (OSSystem.constructedSchwinger osInputs group)
        (OSR.reconstructedHilbert reconstruction group)

    positiveSelfAdjointHamiltonianMeaning : ∀ group →
      Top.IsPositiveSelfAdjointHamiltonian S
        (OSR.reconstructedHilbert reconstruction group)
        (OSR.reconstructedHamiltonian reconstruction group)

open CMP119DirectPhysicalH2 public

asLiteralAInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      sequenceLimit limitLaws quotient division S} →
  CMP119DirectPhysicalH2
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    EuclideanAction Permutation Epsilon Witness
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S →
  LiteralA.PinnedCMP119LiteralAInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws}
    {quotient = quotient}
    {division = division}
    {S = S}
    (osInputs source)
    (reconstruction source)
asLiteralAInputs source = record
  { LiteralA.PinnedCMP119LiteralAInputs.finiteVolumeCutoffMeasure =
      finiteVolumeCutoffMeasure source
  ; LiteralA.PinnedCMP119LiteralAInputs.reflectionPositiveRegularization =
      reflectionPositiveRegularization source
  ; LiteralA.PinnedCMP119LiteralAInputs.ultravioletYangMillsNormalization =
      ultravioletYangMillsNormalization source
  ; LiteralA.PinnedCMP119LiteralAInputs.asymptoticallyFreeScaleTrajectory =
      asymptoticallyFreeScaleTrajectory source
  ; LiteralA.PinnedCMP119LiteralAInputs.gaugeSymmetryPreserved =
      gaugeSymmetryPreserved source
  ; LiteralA.PinnedCMP119LiteralAInputs.localityPreserved =
      localityPreserved source
  ; LiteralA.PinnedCMP119LiteralAInputs.euclideanCovariancePreserved =
      euclideanCovariancePreserved source
  ; LiteralA.PinnedCMP119LiteralAInputs.reflectionPositivityPreserved =
      reflectionPositivityPreserved source
  ; LiteralA.PinnedCMP119LiteralAInputs.positivityNormalizationPreserved =
      positivityNormalizationPreserved source
  ; LiteralA.PinnedCMP119LiteralAInputs.volumeCutoffCompatibility =
      volumeCutoffCompatibility source
  ; LiteralA.PinnedCMP119LiteralAInputs.continuumLimit =
      continuumLimit source
  ; LiteralA.PinnedCMP119LiteralAInputs.schwingerBelongsToContinuumMeasure =
      schwingerBelongsToContinuumMeasure source
  ; LiteralA.PinnedCMP119LiteralAInputs.acceptedWightmanOrOSAxioms =
      acceptedWightmanOrOSAxioms source
  ; LiteralA.PinnedCMP119LiteralAInputs.reconstructedHilbertSpaceMeaning =
      reconstructedHilbertSpaceMeaning source
  ; LiteralA.PinnedCMP119LiteralAInputs.positiveSelfAdjointHamiltonianMeaning =
      positiveSelfAdjointHamiltonianMeaning source
  }

compiledFinite :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      sequenceLimit limitLaws quotient division S}
    (source :
      CMP119DirectPhysicalH2
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S) →
  Pinned.PinnedFiniteYMConstruction S
compiledFinite source =
  LiteralA.compilePinnedFinite (asLiteralAInputs source)

compiledContinuum :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      sequenceLimit limitLaws quotient division S}
    (source :
      CMP119DirectPhysicalH2
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S) →
  Pinned.PinnedContinuumYMConstruction S (compiledFinite source)
compiledContinuum source =
  LiteralA.compilePinnedContinuum (asLiteralAInputs source)

directCMP119H2ObjectConstructionLevel : ProofLevel
directCMP119H2ObjectConstructionLevel = machineChecked

-- Remaining physical payment is now the preferred published/source finite-OS
-- object itself (R462: finite Euclidean/bosonic symmetry, Wilson RP, OS0/OS5
-- finite estimates/closure, selected OS4) plus literal interpretation of the
-- exact finite/continuum/OS objects it constructs.  R436/R424 remain stronger
-- audit/fallback producers and are no longer prerequisites of this H2 ABI.
directCMP119H2PreferredFiniteOSSourceLevel : ProofLevel
directCMP119H2PreferredFiniteOSSourceLevel =
  R581.literalRound581PublishedFiniteOSMomentSourceLevel

directCMP119H2PhysicalInstantiationLevel : ProofLevel
directCMP119H2PhysicalInstantiationLevel = conditional

------------------------------------------------------------------------
-- Current H2 cut after the preferred-source refactor.
------------------------------------------------------------------------

explicitHaarReconstructionRequiredByH2 : Bool
explicitHaarReconstructionRequiredByH2 = false

explicitPeterWeylReconstructionRequiredByH2 : Bool
explicitPeterWeylReconstructionRequiredByH2 = false

projectiveProkhorovRequiredByH2 : Bool
projectiveProkhorovRequiredByH2 = false

independentOS05SourceRequiredByH2 : Bool
independentOS05SourceRequiredByH2 = false

legacyPinnedSystemStillCarriesOS4 : Bool
legacyPinnedSystemStillCarriesOS4 = true

explicitHaarReconstructionRequiredByH2IsFalse :
  explicitHaarReconstructionRequiredByH2 ≡ false
explicitHaarReconstructionRequiredByH2IsFalse = refl

explicitPeterWeylReconstructionRequiredByH2IsFalse :
  explicitPeterWeylReconstructionRequiredByH2 ≡ false
explicitPeterWeylReconstructionRequiredByH2IsFalse = refl

projectiveProkhorovRequiredByH2IsFalse :
  projectiveProkhorovRequiredByH2 ≡ false
projectiveProkhorovRequiredByH2IsFalse = refl

independentOS05SourceRequiredByH2IsFalse :
  independentOS05SourceRequiredByH2 ≡ false
independentOS05SourceRequiredByH2IsFalse = refl

legacyPinnedSystemStillCarriesOS4IsTrue :
  legacyPinnedSystemStillCarriesOS4 ≡ true
legacyPinnedSystemStillCarriesOS4IsTrue = refl
