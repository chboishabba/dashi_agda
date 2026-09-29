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
open import Agda.Builtin.Nat using (Nat; _+_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; 1ℝ; _+ℝ_; _-ℝ_; _*ℝ_; absℝ; _<ℝ_)
open import Data.Product using (Σ; _×_; _,_)
open import Agda.Builtin.List using (List; []; _∷_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayCMP119DirectPhysicalH2CoreExact as H2Core
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as Wilson
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119CovarianceCarrierExact as Carrier
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
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

------------------------------------------------------------------------
-- The generating class is the FINITE REAL LINEAR SPAN OF LITERAL WILSON
-- LOOP PRODUCTS.  In particular, a source cannot set WilsonProduct to all
-- cylinder functions and claim density by the identity embedding.
------------------------------------------------------------------------

literalFiniteWilsonSpan :
  ∀ {Loop Configuration} →
  Wilson.WilsonCylinderBoundData Loop (Configuration → ℝ) ℝ →
  List (ℝ × List Loop) →
  Configuration → ℝ
literalFiniteWilsonSpan source [] configuration = 0ℝ
literalFiniteWilsonSpan source ((coefficient , loops) ∷ rest) configuration =
  coefficient *ℝ
    Wilson.productLoopObservable source loops configuration
  +ℝ
  literalFiniteWilsonSpan source rest configuration

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
  -- Use the actual CMP119 continuum cylinder observable carrier.  It is
  -- deliberately not an arbitrary caller-selected Set (which could be empty).
  FullTest : Set
  FullTest = Configuration → ℝ

  field
    Loop : Set
    literalWilson :
      Wilson.WilsonCylinderBoundData Loop FullTest ℝ

  WilsonProduct : Set
  WilsonProduct = List (ℝ × List Loop)

  embedWilson : WilsonProduct → FullTest
  embedWilson = literalFiniteWilsonSpan literalWilson

  field
    multiplyWilson : WilsonProduct → WilsonProduct → WilsonProduct
    zeroWilson oneWilson : WilsonProduct
    addWilson : WilsonProduct → WilsonProduct → WilsonProduct
    scaleWilson : ℝ → WilsonProduct → WilsonProduct

    -- Algebra structure is the actual CMP119 cylinder algebra, not merely
    -- a caller-supplied closure label.  We require the same multiplication
    -- used for finite OS2 and the continuum covariance products.
    embedsZero : ∀ configuration →
      embedWilson zeroWilson configuration ≡ 0ℝ
    embedsOne : ∀ configuration →
      embedWilson oneWilson configuration ≡ 1ℝ
    embedsSum : ∀ left right configuration →
      embedWilson (addWilson left right) configuration ≡
        embedWilson left configuration +ℝ
        embedWilson right configuration
    embedsScalar : ∀ scalar test configuration →
      embedWilson (scaleWilson scalar test) configuration ≡
        scalar *ℝ embedWilson test configuration
    embedsCylinderProduct : ∀ left right →
      embedWilson (multiplyWilson left right) ≡
      OS2.multiplyObservable
        (OSSystem.observableAlgebraCore (H2Core.coreInputs h2))
        (embedWilson left) (embedWilson right)

    -- The exact R281 left and right tests must each be represented by
    -- finite literal Wilson combinations; this is not automatic from names.
    selectedLeftIsLiteralWilsonSpan :
      ∀ index →
      Σ WilsonProduct (λ combination →
        R278.left (RealGap.testsCore application) index
        ≡ embedWilson combination)

    selectedRightIsLiteralWilsonSpan :
      ∀ index →
      Σ WilsonProduct (λ combination →
        R278.right (RealGap.testsCore application) index
        ≡ embedWilson combination)

    translateWilson : WilsonProduct → Nat → WilsonProduct
    translateFull : FullTest → Nat → FullTest
    inverseTranslateFull : FullTest → Nat → FullTest

    -- At minimum, the proposed time translation must be a genuine
    -- injective action.  A degenerate operation sending everything to zero
    -- is therefore not an acceptable OS4 translation.
    translateAtZero : ∀ test →
      translateFull test 0 ≡ test
    translateComposition : ∀ test first second →
      translateFull (translateFull test first) second
      ≡ translateFull test (first + second)
    inverseTranslationLaw : ∀ test time →
      inverseTranslateFull (translateFull test time) time ≡ test

    translateEmbedding :
      ∀ test time →
      embedWilson (translateWilson test time)
      ≡ translateFull (embedWilson test) time

  -- Connected correlation magnitude is a DEFINITION on the exact H2
  -- normalized continuum expectation, not a freely chosen function.  The
  -- Schwinger-family argument is a presentation of the same CMP119 measure;
  -- the two observable arguments determine the actual connected covariance.
  connectedSchwinger :
    Physical.PhysicalSchwingerFamily (Configuration → ℝ) Position ℝ →
    FullTest → FullTest → Nat → ℝ
  connectedSchwinger _ left right time =
    let
      core = H2Core.coreInputs h2
      dataSet =
        Carrier.cmp119PhysicalMeasureConvergenceDataFromFamily
          (OSSystem.familyCore core group)
          (OSSystem.observableAlgebraCore core)
      extension =
        Cov.realCovarianceExtensionFromFamily
          (OSSystem.familyCore core group)
          (OSSystem.observableAlgebraCore core)
          covarianceLaws
    in
    R278.connectedCovarianceMagnitude extension
      (Gram.continuumMeasure dataSet) left right

  -- The pre-Hilbert OS quadratic form is defined on the EXACT CMP119
  -- continuum expectation and its physical cylinder reflection/multiplication.
  -- This is the Gram-SQUARED distance; its null quotient/completion is the
  -- actual OS Hilbert topology only on the admissible positive-time class.
  osGramSquaredDistance : FullTest → FullTest → ℝ
  osGramSquaredDistance left right =
    let
      core = H2Core.coreInputs h2
      diff = λ configuration →
        left configuration -ℝ right configuration
      algebra = OSSystem.observableAlgebraCore core
    in
    Limit.limitExpectation (OSSystem.familyCore core group)
      (OS2.multiplyObservable algebra
        (OS2.reflectObservable algebra diff) diff)

  field
    -- Decay means actual convergence to zero in the existing real
    -- sequence-limit structure.  There is no custom/vacuous decay predicate.

    -- The OS Gram-squared norm replaces impossible/overstrong global
    -- sup-norm density on an unbounded continuum test space.  An actual
    -- physical positive-time class/completion is still required upstream.
    wilsonProductsUniformlyDense :
      ∀ (test : FullTest) epsilon →
      0ℝ <ℝ epsilon →
      Σ WilsonProduct (λ wilson →
        absℝ (osGramSquaredDistance test
          (embedWilson wilson)) <ℝ epsilon)

    -- Pair-local continuity is sufficient and is mathematically weaker
    -- than global equicontinuity of a bilinear form on an unbounded test
    -- space.  The modulus may depend on (left,right), but not on time.
    uniformlyContinuousConnectedCovariance :
      ∀ (left right : FullTest) epsilon →
      0ℝ <ℝ epsilon →
      Σ ℝ (λ delta →
        (0ℝ <ℝ delta) ×
        (∀ left' right' time →
        absℝ (osGramSquaredDistance left left') <ℝ delta →
        absℝ (osGramSquaredDistance right right') <ℝ delta →
        absℝ
          (connectedSchwinger
            (OSSystem.constructedSchwingerCore
              (H2Core.coreInputs h2) group)
            left (translateFull right time) time -ℝ
           connectedSchwinger
            (OSSystem.constructedSchwingerCore
              (H2Core.coreInputs h2) group)
            left' (translateFull right' time) time)
        <ℝ epsilon))

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
      (∀ (test : FullTest) epsilon →
        0ℝ <ℝ epsilon →
        Σ WilsonProduct (λ wilson →
          absℝ (osGramSquaredDistance test
            (embedWilson wilson)) <ℝ epsilon)) →
      (∀ (left right : FullTest) epsilon →
        0ℝ <ℝ epsilon →
        Σ ℝ (λ delta →
          (0ℝ <ℝ delta) ×
          (∀ left' right' time →
          absℝ (osGramSquaredDistance left left') <ℝ delta →
          absℝ (osGramSquaredDistance right right') <ℝ delta →
          absℝ
            (connectedSchwinger
              (OSSystem.constructedSchwingerCore
                (H2Core.coreInputs h2) group)
              left (translateFull right time) time -ℝ
             connectedSchwinger
              (OSSystem.constructedSchwingerCore
                (H2Core.coreInputs h2) group)
              left' (translateFull right' time) time)
          <ℝ epsilon))) →
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
    (wilsonProductsUniformlyDense meaning)
    (uniformlyContinuousConnectedCovariance meaning)

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
