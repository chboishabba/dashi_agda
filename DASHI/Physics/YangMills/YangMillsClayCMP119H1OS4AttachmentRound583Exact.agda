{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCMP119H1OS4AttachmentRound583Exact where

------------------------------------------------------------------------
-- GOAL-1 H1 -> H2 / ROUND583:
-- THE EXACT PRE-GAP H1 CLUSTERING THEOREM IS THE OS4 ATTACHMENT.
--
-- H2 core has already constructed the Schwinger family and OS reconstruction
-- without clustering.  The selected real CMP116/R281 application now also runs
-- on that same pre-gap core.  The only remaining semantic theorem is that this
-- exact selected continuum clustering statement is the OS4 predicate required
-- for the same Schwinger family.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayCMP119DirectPhysicalH2CoreExact as H2Core
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119CovarianceCarrierExact as Carrier
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.YangMillsClayCMP119RealSelectedGapExact as RealGap
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

ExactSelectedCoreClustering :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      Scale Volume Root SourceDirection SpectralObservable Energy
      sequenceLimit limitLaws quotient division S}
    {h2 :
      H2Core.CMP119DirectPhysicalH2Core
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S}
    {covarianceLaws : Cov.CanonicalRealCovarianceLimitLaws sequenceLimit}
    {group : G}
    {source :
      CMP116.PublishedCMP116DifferentiatedLocalization
        Scale Volume Root SourceDirection ℝ} →
  RealGap.CMP119CoreRealSelectedSpectrumApplication
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vector
    Scale Volume Root SourceDirection SpectralObservable Energy
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws}
    {quotient = quotient}
    {division = division}
    {S = S}
    (H2Core.coreInputs h2)
    covarianceLaws
    group
    source →
  Set
ExactSelectedCoreClustering
    {h2 = h2} {covarianceLaws = covarianceLaws} {group = group}
    application =
  let
    core = H2Core.coreInputs h2
    family = OSSystem.familyCore core group
    algebra = OSSystem.observableAlgebraCore core
    dataSet =
      Carrier.cmp119PhysicalMeasureConvergenceDataFromFamily family algebra
    extension =
      Cov.realCovarianceExtensionFromFamily family algebra covarianceLaws
    tests = RealGap.testsCore application
    spectrum = RealGap.spectrumSourceCore application
  in
  ∀ observable time →
    let index = R281.indexFor spectrum observable time
    in
    R281.LessEqual spectrum
      (R278.connectedCovarianceMagnitude extension
        (Gram.continuumMeasure dataSet)
        (R278.left tests index)
        (R278.right tests index))
      (R281.clusteringEnvelope spectrum observable time)

record CMP119CoreH1OS4Meaning
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
     EuclideanAction Permutation Epsilon Witness
     Scale Volume Root SourceDirection SpectralObservable Energy : Set)
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
    (source :
      CMP116.PublishedCMP116DifferentiatedLocalization
        Scale Volume Root SourceDirection ℝ)
    (application :
      RealGap.CMP119CoreRealSelectedSpectrumApplication
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vector
        Scale Volume Root SourceDirection SpectralObservable Energy
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = S}
        (H2Core.coreInputs h2)
        covarianceLaws
        group
        source)
    : Set₂ where
  field
    -- The admitted full gauge-invariant Schwinger test class is explicit.
    -- Do not confuse one selected Wilson pair with this entire class.
    FullTest : Set
    WilsonProduct : Set
    embedWilson : WilsonProduct → FullTest
    multiplyWilson : WilsonProduct → WilsonProduct → WilsonProduct
    translateWilson : WilsonProduct → Nat → WilsonProduct
    translateFull : FullTest → Nat → FullTest

    translateEmbedding :
      ∀ test time →
      embedWilson (translateWilson test time)
      ≡ translateFull (embedWilson test) time

    -- True connected correlations of the SAME reconstructed Schwinger family
    -- on the full physical test class (including vacuum subtraction).
    connectedSchwinger :
      Physical.PhysicalSchwingerFamily (Configuration → ℝ) Position ℝ →
      FullTest → FullTest → Nat → ℝ

    -- Decay means actual convergence to zero in the existing real
    -- sequence-limit structure.  There is no custom/vacuous decay predicate.

    WilsonProductsFormAlgebra : Set
    wilsonProductsFormAlgebra : WilsonProductsFormAlgebra

    WilsonProductsDenseInPhysicalSector : Set
    wilsonProductsDenseInPhysicalSector :
      WilsonProductsDenseInPhysicalSector

    UniformCorrelationContinuity : Set
    uniformCorrelationContinuity : UniformCorrelationContinuity

    -- Genuine source/weld theorem, not a compiler-created equality:
    -- the exact R281 selected Wilson estimate applies to EVERY member of the
    -- chosen Wilson-product determining class under time translation.
    selectedEstimateCoversWilsonProducts :
      ExactSelectedCoreClustering application →
      ∀ left right →
      RealLimit.Converges sequenceLimit
        (λ time →
          connectedSchwinger
            (OSSystem.constructedSchwingerCore
              (H2Core.coreInputs h2) group)
            (embedWilson left)
            (translateFull (embedWilson right) time)
            time) 0ℝ

    -- Analytic closure theorem: density plus uniform continuity extends
    -- selected Wilson-product clustering to ALL admitted Schwinger tests.
    -- Its proof is the remaining OS4 physical analysis, not an automatic
    -- consequence of R281's selected covariance inequality.
    denseWilsonClusteringExtendsToFullTestClass :
      (∀ left right →
        RealLimit.Converges sequenceLimit
          (λ time →
            connectedSchwinger
              (OSSystem.constructedSchwingerCore
                (H2Core.coreInputs h2) group)
              (embedWilson left)
              (translateFull (embedWilson right) time)
              time) 0ℝ) →
      WilsonProductsFormAlgebra →
      WilsonProductsDenseInPhysicalSector →
      UniformCorrelationContinuity →
      ∀ left right →
      RealLimit.Converges sequenceLimit
        (λ time →
          connectedSchwinger
            (OSSystem.constructedSchwingerCore
              (H2Core.coreInputs h2) group)
            left (translateFull right time) time) 0ℝ

open CMP119CoreH1OS4Meaning public

-- Fix OS4 to full physical Schwinger-test clustering: a quantified
-- convergence statement, not an arbitrary Set selected by the producer.
FullCoreOS4 :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      Scale Volume Root SourceDirection SpectralObservable Energy
      sequenceLimit limitLaws quotient division S
      h2 covarianceLaws group source application} →
  CMP119CoreH1OS4Meaning
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    EuclideanAction Permutation Epsilon Witness
    Scale Volume Root SourceDirection SpectralObservable Energy
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S
    h2 covarianceLaws group source application →
  Physical.PhysicalSchwingerFamily (Configuration → ℝ) Position ℝ →
  Set
FullCoreOS4 {sequenceLimit = sequenceLimit} meaning family =
  ∀ left right →
  RealLimit.Converges sequenceLimit
    (λ time →
      connectedSchwinger meaning family
        left (translateFull meaning right time) time) 0ℝ

selectedH1ClusteringMeansFullOS4 :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      Scale Volume Root SourceDirection SpectralObservable Energy
      sequenceLimit limitLaws quotient division S
      h2 covarianceLaws group source application}
    (meaning :
      CMP119CoreH1OS4Meaning
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        Scale Volume Root SourceDirection SpectralObservable Energy
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S
        h2 covarianceLaws group source application) →
  ExactSelectedCoreClustering application →
  FullCoreOS4 meaning
    (OSSystem.constructedSchwingerCore
      (H2Core.coreInputs h2) group)
selectedH1ClusteringMeansFullOS4 meaning selected =
  denseWilsonClusteringExtendsToFullTestClass meaning
    (selectedEstimateCoversWilsonProducts meaning selected)
    (wilsonProductsFormAlgebra meaning)
    (wilsonProductsDenseInPhysicalSector meaning)
    (uniformCorrelationContinuity meaning)

asCoreOS4Attachment :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      Scale Volume Root SourceDirection SpectralObservable Energy
      sequenceLimit limitLaws quotient division S
      h2 covarianceLaws group source application} →
  CMP119CoreH1OS4Meaning
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    EuclideanAction Permutation Epsilon Witness
    Scale Volume Root SourceDirection SpectralObservable Energy
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S
    h2 covarianceLaws group source application →
  OSGap.OS4Attachment
    (OSSystem.continuumOSCoreSystem
      (H2Core.coreInputs h2) group)
asCoreOS4Attachment meaning = record
  { OSGap.OS4Attachment.OS4ClusteringAttached =
      FullCoreOS4 meaning
        (OSSystem.constructedSchwingerCore
          (H2Core.coreInputs h2) group)
  ; OSGap.OS4Attachment.os4Attached =
      selectedH1ClusteringMeansFullOS4 meaning
        (RealGap.selectedCoreContinuumCovarianceBelowSpectrumEnvelope
          _)
  }

round583H1ToOS4CompilerLevel : ProofLevel
round583H1ToOS4CompilerLevel = machineChecked

-- This is the one genuine semantic attachment: interpret the exact selected H1
-- continuum clustering theorem as OS4 for the exact H2 core Schwinger family.
literalRound583SelectedClusteringMeansOS4Level : ProofLevel
literalRound583SelectedClusteringMeansOS4Level = conditional
