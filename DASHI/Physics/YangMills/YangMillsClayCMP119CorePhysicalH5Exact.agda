{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCMP119CorePhysicalH5Exact where

------------------------------------------------------------------------
-- H5 CONTINUATION ON PRE-GAP CMP119, WITHOUT THE OS4 CYCLE.
--
-- Per-group physical source is constructed on ONE core finite family:
--  quantitative Lie data -> five-block / selected real H1-R281
--  -> Wilson-product presentation + physical OS4 dense-class extension
--  -> same-core-H R331/semigroup/cyclic spectral identification.
--
-- Once *every* group has supplied the relevant OS4 meaning, assemble one
-- global OS4 attachment, then compile historical H2/H5 source records.  This
-- prevents H5 from requiring the full clustered H2 before providing H1.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (_×_)
open import Data.Rational.Base using (ℚ)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.CompactSimpleQuantitativeCoverage as Compact
import DASHI.Physics.YangMills.BalabanGroupParametricFiveBlockSignedG2Exact as FiveBlock
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayCMP119DirectPhysicalH2CoreExact as H2Core
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem
import DASHI.Physics.YangMills.YangMillsClayCMP119RealSelectedGapExact as RealGap
import DASHI.Physics.YangMills.YangMillsClayCMP119RealSelectedWilsonH2Exact as Wilson
import DASHI.Physics.YangMills.YangMillsClayCMP119H1OS4AttachmentRound583Exact as R583
import DASHI.Physics.YangMills.YangMillsClayCMP119CoreSemigroupH3Exact as H3Core
import DASHI.Physics.YangMills.BalabanOSIndexedTransferCoordinateRound331Exact as R331
import DASHI.Physics.YangMills.BalabanTransferEnergyDecayRatioCoordinateRound302Exact as R302
import DASHI.Physics.YangMills.YangMillsClayCMP119CompactSimplePhysicalH5Exact as LegacyH5
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record CMP119CoreGroupPhysicalPackage
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
     EuclideanAction Permutation Epsilon Witness
     LieElement GroupElement : Set)
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
    (h2 :
      H2Core.CMP119DirectPhysicalH2Core
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (covarianceLaws : Cov.CanonicalRealCovarianceLimitLaws sequenceLimit)
    (group : G)
    (classifiedGroup : Compact.CompactSimpleLieGroup)
    (quantitative :
      Compact.QuantitativeCompactLiePackage
        ℚ LieElement GroupElement classifiedGroup) : Set₂ where
  field
    fiveBlock :
      FiveBlock.GroupParametricFiveBlockG2Data
        LieElement GroupElement classifiedGroup

    fiveBlockUsesQuantitativePackage :
      FiveBlock.quantitativeLiePackage fiveBlock ≡ quantitative

    SourceScale SourceVolume SourceRoot SourceDirection SpectralObservable : Set

    publishedCMP116 :
      CMP116.PublishedCMP116DifferentiatedLocalization
        SourceScale SourceVolume SourceRoot SourceDirection ℝ

    realSelectedCore :
      RealGap.CMP119CoreRealSelectedSpectrumApplication
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vector
        SourceScale SourceVolume SourceRoot SourceDirection
        SpectralObservable ℚ
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = S}
        (H2Core.coreInputs h2) covarianceLaws group publishedCMP116

    h1OS4Meaning :
      R583.CMP119CoreH1OS4Meaning
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        SourceScale SourceVolume SourceRoot SourceDirection
        SpectralObservable ℚ
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S
        h2 covarianceLaws group publishedCMP116 realSelectedCore


  -- H5 and R583 must use the same literal loop carrier, not two
  -- independently selected types with a later coercion.
  Loop : Set
  Loop = R583.Loop h1OS4Meaning

  field
    selectedWilsonCore :
      Wilson.CMP119CoreSelectedWilsonPresentation
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vector Loop
        (H2Core.coreInputs h2) covarianceLaws group
        (RealGap.testsCore realSelectedCore)

    -- The full determining span and the R281-selected Wilson products
    -- share the exact physical loop-observable generator.
    sameLiteralWilsonCylinder :
      R583.literalWilson h1OS4Meaning
      ≡ Wilson.wilsonCore selectedWilsonCore

    positiveGapCandidate :
      Gap.PositiveEnergy
        (R281.asReconstructedClusteringSpectrum
          (RealGap.spectrumSourceCore realSelectedCore))
        (Gap.gapCandidate
          (R281.asReconstructedClusteringSpectrum
            (RealGap.spectrumSourceCore realSelectedCore)))


    -- Full accepted-OS interpretation of this exact Schwinger family is a
    -- separate physical/semantic payment, not supplied by a bare OS4 record.
    acceptedWightmanOrOSAxioms :
      Top.SatisfiesAcceptedWightmanOrOSAxioms S group
        (OSSystem.constructedSchwingerCore
          (H2Core.coreInputs h2) group)

    coreSameOSH3 :
      H3Core.CMP119CoreSemigroupH3
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        SourceScale SourceVolume SourceRoot SourceDirection
        SpectralObservable
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S
        h2 covarianceLaws group publishedCMP116 realSelectedCore

    -- The pre-gap H3 autocorrelation and R583 OS4 must use identical
    -- Euclidean-time translates of the very SAME cylinder Wilson function.
    -- This remains a physical identification rather than an extra selector.
    coreOS4TimeTranslationIsH3TimeTranslation :
      ∀ wilson time →
      R583.translateFull h1OS4Meaning wilson time
      ≡ H3Core.translatePhysicalWilson coreSameOSH3 wilson time

open CMP119CoreGroupPhysicalPackage public

record CMP119CompactSimplePhysicalH5Core
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
     EuclideanAction Permutation Epsilon Witness
     LieElement GroupElement : Set)
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
    (h2 :
      H2Core.CMP119DirectPhysicalH2Core
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (covarianceLaws : Cov.CanonicalRealCovarianceLimitLaws sequenceLimit)
    : Set₂ where
  field
    authority :
      Compact.CompactSimpleQuantitativeAuthority
        ℚ LieElement GroupElement

    literalToClassified :
      G → Compact.CompactSimpleLieGroup

    -- The canonical family index must describe a genuinely simple
    -- compact group, not a degenerate classical rank accepted only by
    -- the unrestricted historical numerical package.
    literalGroupHasValidSimpleIndex :
      ∀ group →
      Compact.ValidCompactSimpleIndex (literalToClassified group)

    -- The image of the literal group carrier actually covers ALL
    -- classified compact simple groups, not just a convenient finite
    -- subfamily.  The witness must retain the SAME group when H1/H2/H3
    -- are instantiated downstream.
    everyValidClassifiedGroupHasLiteralRepresentative :
      ∀ classified →
      Compact.ValidCompactSimpleIndex classified →
      Σ G (λ group → literalToClassified group ≡ classified)

    quantitativePackageMeansLiteralCompactSimple :
      ∀ group →
      Compact.QuantitativeCompactLiePackage
        ℚ LieElement GroupElement (literalToClassified group) →
      Top.IsCompactSimple S group

    classificationMeansParameterizationPreserved :
      (∀ group →
        Compact.QuantitativeCompactLiePackage
          ℚ LieElement GroupElement (literalToClassified group)) →
      Top.CompactSimpleParameterizationPreserved S

    continueCorePhysicalPackage :
      (group : G) →
      (quantitative :
        Compact.QuantitativeCompactLiePackage
          ℚ LieElement GroupElement (literalToClassified group)) →
      CMP119CoreGroupPhysicalPackage
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        LieElement GroupElement
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S
        h2 covarianceLaws group (literalToClassified group) quantitative

open CMP119CompactSimplePhysicalH5Core public

corePhysicalPackageForGroup :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness LieElement GroupElement
      sequenceLimit limitLaws quotient division S h2 covarianceLaws}
    (h5 :
      CMP119CompactSimplePhysicalH5Core
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        LieElement GroupElement
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2 covarianceLaws)
    group →
  CMP119CoreGroupPhysicalPackage
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    EuclideanAction Permutation Epsilon Witness
    LieElement GroupElement
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S h2 covarianceLaws
    group (literalToClassified h5 group)
    (Compact.compactSimpleHasQuantitativePackage
      (authority h5) (literalToClassified h5 group))
corePhysicalPackageForGroup h5 group =
  continueCorePhysicalPackage h5 group
    (Compact.compactSimpleHasQuantitativePackage
      (authority h5) (literalToClassified h5 group))

------------------------------------------------------------------------
-- The classification-complete physical constructor is exposed on the
-- classified group argument.  It witnesses an actual literal CMP119
-- representative and that representative's quantitative H1/H2/H3 package.
-- No SU(2)-only or sparse group carrier can inhabit this theorem.
------------------------------------------------------------------------

classifiedCompactSimplePhysicalPackage :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness LieElement GroupElement
      sequenceLimit limitLaws quotient division S h2 covarianceLaws}
    (h5 :
      CMP119CompactSimplePhysicalH5Core
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        LieElement GroupElement
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2 covarianceLaws)
    (classified : Compact.CompactSimpleLieGroup) →
  Compact.ValidCompactSimpleIndex classified →
  Σ G (λ group →
    (literalToClassified h5 group ≡ classified) ×
    CMP119CoreGroupPhysicalPackage
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      LieElement GroupElement
      {sequenceLimit = sequenceLimit}
      limitLaws quotient division S h2 covarianceLaws
      group (literalToClassified h5 group)
      (Compact.compactSimpleHasQuantitativePackage
        (authority h5) (literalToClassified h5 group)))
classifiedCompactSimplePhysicalPackage h5 classified valid
  with everyValidClassifiedGroupHasLiteralRepresentative h5 classified valid
... | group , sameClassified =
  group , (sameClassified , corePhysicalPackageForGroup h5 group)

------------------------------------------------------------------------
-- All-group gap normalization is not another physical assumption: each
-- group uses its OWN exact H2-core H3 transfer coordinate and the candidate
-- equality already stored by that core H3 source.
------------------------------------------------------------------------

coreGroupGapIsSameHTransferEnergy :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness LieElement GroupElement
      sequenceLimit limitLaws quotient division S h2 covarianceLaws}
    (h5 :
      CMP119CompactSimplePhysicalH5Core
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        LieElement GroupElement
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2 covarianceLaws)
    group →
  let package = corePhysicalPackageForGroup h5 group
  in
  Gap.gapCandidate
    (R281.asReconstructedClusteringSpectrum
      (RealGap.spectrumSourceCore (realSelectedCore package)))
  ≡
  R302.candidateEnergy
    (R331.coordinateCore
      (H3Core.indexedTransfer (coreSameOSH3 package)))
coreGroupGapIsSameHTransferEnergy h5 group =
  H3Core.selectedGapIsTransferCandidate
    (coreSameOSH3 (corePhysicalPackageForGroup h5 group))

coreH5OS4Attachment :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness LieElement GroupElement
      sequenceLimit limitLaws quotient division S h2 covarianceLaws}
    (h5 :
      CMP119CompactSimplePhysicalH5Core
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        LieElement GroupElement
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2 covarianceLaws) →
  H2Core.CMP119DirectPhysicalH2OS4Attachment h2
coreH5OS4Attachment {h2 = h2} h5 = record
  { H2Core.CMP119DirectPhysicalH2OS4Attachment.OS4Clustering =
      λ group →
        R583.FullCoreOS4
          (h1OS4Meaning (corePhysicalPackageForGroup h5 group))
          (OSSystem.constructedSchwingerCore
            (H2Core.coreInputs h2) group)
  ; H2Core.CMP119DirectPhysicalH2OS4Attachment.os4 =
      λ group →
        R583.selectedH1ClusteringMeansFullOS4
          (h1OS4Meaning (corePhysicalPackageForGroup h5 group))
          (RealGap.selectedCoreContinuumCovarianceBelowSpectrumEnvelope
            (realSelectedCore (corePhysicalPackageForGroup h5 group)))
  ; H2Core.CMP119DirectPhysicalH2OS4Attachment.acceptedWightmanOrOSAxioms =
      λ group →
        acceptedWightmanOrOSAxioms
          (corePhysicalPackageForGroup h5 group)
  }

coreH5AsLegacy :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness LieElement GroupElement
      sequenceLimit limitLaws quotient division S h2 covarianceLaws} →
  (h5 :
    CMP119CompactSimplePhysicalH5Core
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      LieElement GroupElement
      {sequenceLimit = sequenceLimit}
      limitLaws quotient division S h2 covarianceLaws) →
  LegacyH5.CMP119CompactSimplePhysicalH5
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    EuclideanAction Permutation Epsilon Witness
    LieElement GroupElement
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S
    (H2Core.asLegacyH2 h2 (coreH5OS4Attachment h5))
    covarianceLaws
coreH5AsLegacy {h2 = h2} {covarianceLaws = covarianceLaws} h5 = record
  { LegacyH5.CMP119CompactSimplePhysicalH5.authority =
      authority h5
  ; LegacyH5.CMP119CompactSimplePhysicalH5.literalToClassified =
      literalToClassified h5
  ; LegacyH5.CMP119CompactSimplePhysicalH5.quantitativePackageMeansLiteralCompactSimple =
      quantitativePackageMeansLiteralCompactSimple h5
  ; LegacyH5.CMP119CompactSimplePhysicalH5.classificationMeansParameterizationPreserved =
      classificationMeansParameterizationPreserved h5
  ; LegacyH5.CMP119CompactSimplePhysicalH5.continuePhysicalPackage =
      λ group quantitative →
        let
          package = continueCorePhysicalPackage h5 group quantitative
          clustering = coreH5OS4Attachment h5
        in record
          { LegacyH5.CMP119GroupPhysicalPackage.fiveBlock =
              fiveBlock package
          ; LegacyH5.CMP119GroupPhysicalPackage.fiveBlockUsesQuantitativePackage =
              fiveBlockUsesQuantitativePackage package
          ; LegacyH5.CMP119GroupPhysicalPackage.SourceScale =
              SourceScale package
          ; LegacyH5.CMP119GroupPhysicalPackage.SourceVolume =
              SourceVolume package
          ; LegacyH5.CMP119GroupPhysicalPackage.SourceRoot =
              SourceRoot package
          ; LegacyH5.CMP119GroupPhysicalPackage.SourceDirection' =
              SourceDirection package
          ; LegacyH5.CMP119GroupPhysicalPackage.SpectralObservable' =
              SpectralObservable package
          ; LegacyH5.CMP119GroupPhysicalPackage.publishedCMP116 =
              publishedCMP116 package
          ; LegacyH5.CMP119GroupPhysicalPackage.realSelected =
              RealGap.coreSelectedAsLegacy
                (H2Core.coreInputs h2)
                (H2Core.asPinnedOS4Attachment clustering)
                (realSelectedCore package)
          ; LegacyH5.CMP119GroupPhysicalPackage.Loop =
              Loop package
          ; LegacyH5.CMP119GroupPhysicalPackage.selectedWilson =
              Wilson.coreWilsonAsLegacy
                (H2Core.coreInputs h2)
                (H2Core.asPinnedOS4Attachment clustering)
                covarianceLaws
                group
                (RealGap.testsCore (realSelectedCore package))
                (selectedWilsonCore package)
          ; LegacyH5.CMP119GroupPhysicalPackage.positiveGapCandidate =
              positiveGapCandidate package
          ; LegacyH5.CMP119GroupPhysicalPackage.sameOSH3 =
              H3Core.coreH3AsLegacy
                h2 clustering (coreSameOSH3 package)
          }
  }

coreH5AllGroupOS4AssemblyLevel : ProofLevel
coreH5AllGroupOS4AssemblyLevel = machineChecked

coreH5LegacyCompatibilityLevel : ProofLevel
coreH5LegacyCompatibilityLevel = machineChecked

-- Physical continuation includes actual all-G quantitative estimates, exact
-- real selected R281 application, full Wilson test-class closure to OS4,
-- semigroup spectral meaning and accepted continuum interpretation.
coreH5PhysicalContinuationLevel : ProofLevel
coreH5PhysicalContinuationLevel = conditional
