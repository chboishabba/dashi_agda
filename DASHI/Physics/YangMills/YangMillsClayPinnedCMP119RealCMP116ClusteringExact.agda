{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ClusteringExact where

------------------------------------------------------------------------
-- LITERAL CMP116 ON THE SAME REAL CMP119 COVARIANCE
--
-- Selected source response = finite real connected covariance at each cutoff.
-- Published CMP116 localization then bounds that exact covariance, and closed
-- order passes the bound to the SAME continuum covariance.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119CovarianceCarrierExact as Carrier
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record RealUpperClosedLimit
    (sequenceLimit : Seq.RealSequenceLimitByVanishingError) : Set₁ where
  field
    upperClosed :
      (sequence : Nat → ℝ) (target upper : ℝ) →
      RealLimit.Converges sequenceLimit sequence target →
      (∀ cutoff → sequence cutoff ≤ℝ upper) →
      target ≤ℝ upper

open RealUpperClosedLimit public

------------------------------------------------------------------------
-- PRE-GAP H1 CLUSTERING INPUT.
--
-- Same theorem as the historical carrier, but indexed only by the CMP119 OS
-- core.  No OS4/full clustered system is available or required here.
------------------------------------------------------------------------

record LiteralRealCMP116CoreClusteringInputs
    (CompactSimpleGroup Spacetime Configuration Position
     CurvaturePolynomial LocalOperator OPECoefficient StressTensor
     HilbertSpace Hamiltonian VacuumState
     Scale Volume Root SourceDirection Index : Set)
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
    (a :
      A.PinnedCMP119OSCoreInputs
        CompactSimpleGroup Spacetime Configuration Position
        CurvaturePolynomial LocalOperator OPECoefficient StressTensor
        HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (covarianceLaws : Cov.CanonicalRealCovarianceLimitLaws sequenceLimit)
    (group : CompactSimpleGroup)
    (source :
      CMP116.PublishedCMP116DifferentiatedLocalization
        Scale Volume Root SourceDirection ℝ) : Set₂ where
  private
    family = A.familyCore a group
    algebra = A.observableAlgebraCore a
    dataSet =
      Carrier.cmp119PhysicalMeasureConvergenceDataFromFamily family algebra
    extension =
      Cov.realCovarianceExtensionFromFamily family algebra covarianceLaws

  field
    leftCore rightCore : Index → Configuration → ℝ

    sourceLeftCore sourceRightCore : Index → SourceDirection

    scaleAtCore : Nat → Scale
    volumeAtCore : Nat → Volume

    selectedPairAdmissibleCore : ∀ cutoff index →
      CMP116.AdmissibleSourcePair source
        (scaleAtCore cutoff) (volumeAtCore cutoff)
        (sourceLeftCore index) (sourceRightCore index)

    sourceMagnitudeIsFinitePhysicalCovarianceCore :
      ∀ cutoff index →
      CMP116.differentiatedMagnitude source
        (scaleAtCore cutoff) (volumeAtCore cutoff)
        (sourceLeftCore index) (sourceRightCore index)
      ≡
      R278.connectedCovarianceMagnitude extension
        (Gram.measureSequence dataSet cutoff)
        (leftCore index) (rightCore index)

    physicalUpperCore : Index → ℝ

    sourceEnvelopeBelowPhysicalUpperCore :
      ∀ cutoff index →
      CMP116.sourceEnvelope source
        (scaleAtCore cutoff) (volumeAtCore cutoff)
        (CMP116.sourceRoot source
          (scaleAtCore cutoff) (volumeAtCore cutoff)
          (sourceLeftCore index) (sourceRightCore index))
        (CMP116.sourceDistance source
          (sourceLeftCore index) (sourceRightCore index))
      ≤ℝ physicalUpperCore index

    orderLimitCore : RealUpperClosedLimit sequenceLimit

open LiteralRealCMP116CoreClusteringInputs public

finiteCorePhysicalCovarianceBelowUpper :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Scale Volume Root SourceDirection Index
      sequenceLimit limitLaws quotient division S a covarianceLaws group source}
    (inputs :
      LiteralRealCMP116CoreClusteringInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Scale Volume Root SourceDirection Index
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} a covarianceLaws group source)
    cutoff index →
  let
    family = A.familyCore a group
    algebra = A.observableAlgebraCore a
    dataSet =
      Carrier.cmp119PhysicalMeasureConvergenceDataFromFamily family algebra
    extension =
      Cov.realCovarianceExtensionFromFamily family algebra covarianceLaws
  in
  R278.connectedCovarianceMagnitude extension
    (Gram.measureSequence dataSet cutoff)
    (leftCore inputs index) (rightCore inputs index)
  ≤ℝ
  physicalUpperCore inputs index
finiteCorePhysicalCovarianceBelowUpper
    {source = source} inputs cutoff index =
  let
    sourceBound =
      CMP116.sourceDifferentiatedLocalization source
        (scaleAtCore inputs cutoff)
        (volumeAtCore inputs cutoff)
        (sourceLeftCore inputs index)
        (sourceRightCore inputs index)
        (selectedPairAdmissibleCore inputs cutoff index)

    calibrated =
      sourceEnvelopeBelowPhysicalUpperCore inputs cutoff index
  in
  subst
    (λ lower → lower ≤ℝ physicalUpperCore inputs index)
    (sourceMagnitudeIsFinitePhysicalCovarianceCore inputs cutoff index)
    (CMP116.orderTransitive source sourceBound calibrated)

continuumCorePhysicalCovarianceBelowUpper :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Scale Volume Root SourceDirection Index
      sequenceLimit limitLaws quotient division S a covarianceLaws group source}
    (inputs :
      LiteralRealCMP116CoreClusteringInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Scale Volume Root SourceDirection Index
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} a covarianceLaws group source)
    index →
  let
    family = A.familyCore a group
    algebra = A.observableAlgebraCore a
    dataSet =
      Carrier.cmp119PhysicalMeasureConvergenceDataFromFamily family algebra
    extension =
      Cov.realCovarianceExtensionFromFamily family algebra covarianceLaws
  in
  R278.connectedCovarianceMagnitude extension
    (Gram.continuumMeasure dataSet)
    (leftCore inputs index) (rightCore inputs index)
  ≤ℝ
  physicalUpperCore inputs index
continuumCorePhysicalCovarianceBelowUpper
    {a = a} {covarianceLaws = covarianceLaws} {group = group}
    inputs index =
  RealUpperClosedLimit.upperClosed
    (orderLimitCore inputs)
    (λ cutoff →
      let
        family = A.familyCore a group
        algebra = A.observableAlgebraCore a
        dataSet =
          Carrier.cmp119PhysicalMeasureConvergenceDataFromFamily family algebra
        extension =
          Cov.realCovarianceExtensionFromFamily family algebra covarianceLaws
      in
      R278.connectedCovarianceMagnitude extension
        (Gram.measureSequence dataSet cutoff)
        (leftCore inputs index) (rightCore inputs index))
    (let
       family = A.familyCore a group
       algebra = A.observableAlgebraCore a
       dataSet =
         Carrier.cmp119PhysicalMeasureConvergenceDataFromFamily family algebra
       extension =
         Cov.realCovarianceExtensionFromFamily family algebra covarianceLaws
     in
     R278.connectedCovarianceMagnitude extension
       (Gram.continuumMeasure dataSet)
       (leftCore inputs index) (rightCore inputs index))
    (physicalUpperCore inputs index)
    (Cov.selectedRealConnectedCovarianceConvergesFromFamily
      (A.familyCore a group)
      (A.observableAlgebraCore a)
      covarianceLaws
      _
      (leftCore inputs) (rightCore inputs) index)
    (λ cutoff →
      finiteCorePhysicalCovarianceBelowUpper inputs cutoff index)

record LiteralRealCMP116ClusteringInputs
    (CompactSimpleGroup Spacetime Configuration Position
     CurvaturePolynomial LocalOperator OPECoefficient StressTensor
     HilbertSpace Hamiltonian VacuumState
     Scale Volume Root SourceDirection Index : Set)
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
    (a :
      A.PinnedCMP119OSAxiomInputs
        CompactSimpleGroup Spacetime Configuration Position
        CurvaturePolynomial LocalOperator OPECoefficient StressTensor
        HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (covarianceLaws : Cov.CanonicalRealCovarianceLimitLaws sequenceLimit)
    (group : CompactSimpleGroup)
    (source :
      CMP116.PublishedCMP116DifferentiatedLocalization
        Scale Volume Root SourceDirection ℝ) : Set₂ where
  field
    left right : Index → Configuration → ℝ

    sourceLeft sourceRight : Index → SourceDirection

    scaleAt : Nat → Scale
    volumeAt : Nat → Volume

    selectedPairAdmissible : ∀ cutoff index →
      CMP116.AdmissibleSourcePair source
        (scaleAt cutoff) (volumeAt cutoff)
        (sourceLeft index) (sourceRight index)

    -- L4: the published differentiated response is the literal finite real
    -- connected covariance magnitude on the same CMP119 measure.
    sourceMagnitudeIsFinitePhysicalCovariance :
      ∀ cutoff index →
      CMP116.differentiatedMagnitude source
        (scaleAt cutoff) (volumeAt cutoff)
        (sourceLeft index) (sourceRight index)
      ≡
      R278.connectedCovarianceMagnitude
        (Cov.realCovarianceExtension a covarianceLaws group)
        (Gram.measureSequence
          (Carrier.cmp119PhysicalMeasureConvergenceData a group)
          cutoff)
        (left index) (right index)

    physicalUpper : Index → ℝ

    -- L5: source tree/localization coordinates are calibrated to the desired
    -- physical Euclidean upper.  All source exponential/distance algebra feeds
    -- this single comparison.
    sourceEnvelopeBelowPhysicalUpper :
      ∀ cutoff index →
      CMP116.sourceEnvelope source
        (scaleAt cutoff) (volumeAt cutoff)
        (CMP116.sourceRoot source
          (scaleAt cutoff) (volumeAt cutoff)
          (sourceLeft index) (sourceRight index))
        (CMP116.sourceDistance source
          (sourceLeft index) (sourceRight index))
      ≤ℝ physicalUpper index

    orderLimit : RealUpperClosedLimit sequenceLimit

open LiteralRealCMP116ClusteringInputs public

------------------------------------------------------------------------
-- Transport the SAME pre-gap H1 source through a later OS4 attachment.
-- The normalized family, cylinder algebra, and real covariance data do not
-- change, so this is a definitional compiler, not a second physical source.
------------------------------------------------------------------------

coreH1AsLegacy :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Scale Volume Root SourceDirection Index
      sequenceLimit limitLaws quotient division S}
    (core :
      A.PinnedCMP119OSCoreInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (clustering : A.CMP119OS4Attachment core)
    {covarianceLaws : Cov.CanonicalRealCovarianceLimitLaws sequenceLimit}
    {group : G}
    {source :
      CMP116.PublishedCMP116DifferentiatedLocalization
        Scale Volume Root SourceDirection ℝ} →
  LiteralRealCMP116CoreClusteringInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    Scale Volume Root SourceDirection Index
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S}
    core covarianceLaws group source →
  LiteralRealCMP116ClusteringInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    Scale Volume Root SourceDirection Index
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S}
    (A.corePlusOS4Inputs core clustering)
    covarianceLaws group source
coreH1AsLegacy core clustering source = record
  { LiteralRealCMP116ClusteringInputs.left =
      leftCore source
  ; LiteralRealCMP116ClusteringInputs.right =
      rightCore source
  ; LiteralRealCMP116ClusteringInputs.sourceLeft =
      sourceLeftCore source
  ; LiteralRealCMP116ClusteringInputs.sourceRight =
      sourceRightCore source
  ; LiteralRealCMP116ClusteringInputs.scaleAt =
      scaleAtCore source
  ; LiteralRealCMP116ClusteringInputs.volumeAt =
      volumeAtCore source
  ; LiteralRealCMP116ClusteringInputs.selectedPairAdmissible =
      selectedPairAdmissibleCore source
  ; LiteralRealCMP116ClusteringInputs.sourceMagnitudeIsFinitePhysicalCovariance =
      sourceMagnitudeIsFinitePhysicalCovarianceCore source
  ; LiteralRealCMP116ClusteringInputs.physicalUpper =
      physicalUpperCore source
  ; LiteralRealCMP116ClusteringInputs.sourceEnvelopeBelowPhysicalUpper =
      sourceEnvelopeBelowPhysicalUpperCore source
  ; LiteralRealCMP116ClusteringInputs.orderLimit =
      orderLimitCore source
  }

coreH1ToLegacyAfterOS4CompilerLevel : ProofLevel
coreH1ToLegacyAfterOS4CompilerLevel = machineChecked

finitePhysicalCovarianceBelowUpper :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Scale Volume Root SourceDirection Index
      sequenceLimit limitLaws quotient division S a covarianceLaws group source}
    (inputs :
      LiteralRealCMP116ClusteringInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Scale Volume Root SourceDirection Index
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} a covarianceLaws group source)
    cutoff index →
  R278.connectedCovarianceMagnitude
    (Cov.realCovarianceExtension a covarianceLaws group)
    (Gram.measureSequence
      (Carrier.cmp119PhysicalMeasureConvergenceData a group)
      cutoff)
    (left inputs index) (right inputs index)
  ≤ℝ
  physicalUpper inputs index
finitePhysicalCovarianceBelowUpper
    {source = source} inputs cutoff index =
  let
    sourceBound =
      CMP116.sourceDifferentiatedLocalization source
        (scaleAt inputs cutoff)
        (volumeAt inputs cutoff)
        (sourceLeft inputs index)
        (sourceRight inputs index)
        (selectedPairAdmissible inputs cutoff index)

    calibrated =
      sourceEnvelopeBelowPhysicalUpper inputs cutoff index
  in
  subst
    (λ lower → lower ≤ℝ physicalUpper inputs index)
    (sourceMagnitudeIsFinitePhysicalCovariance inputs cutoff index)
    (CMP116.orderTransitive source sourceBound calibrated)

continuumPhysicalCovarianceBelowUpper :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Scale Volume Root SourceDirection Index
      sequenceLimit limitLaws quotient division S a covarianceLaws group source}
    (inputs :
      LiteralRealCMP116ClusteringInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Scale Volume Root SourceDirection Index
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} a covarianceLaws group source)
    index →
  R278.connectedCovarianceMagnitude
    (Cov.realCovarianceExtension a covarianceLaws group)
    (Gram.continuumMeasure
      (Carrier.cmp119PhysicalMeasureConvergenceData a group))
    (left inputs index) (right inputs index)
  ≤ℝ
  physicalUpper inputs index
continuumPhysicalCovarianceBelowUpper
    {a = a} {covarianceLaws = covarianceLaws} {group = group}
    inputs index =
  RealUpperClosedLimit.upperClosed
    (orderLimit inputs)
    (λ cutoff →
      R278.connectedCovarianceMagnitude
        (Cov.realCovarianceExtension a covarianceLaws group)
        (Gram.measureSequence
          (Carrier.cmp119PhysicalMeasureConvergenceData a group)
          cutoff)
        (left inputs index) (right inputs index))
    (R278.connectedCovarianceMagnitude
      (Cov.realCovarianceExtension a covarianceLaws group)
      (Gram.continuumMeasure
        (Carrier.cmp119PhysicalMeasureConvergenceData a group))
      (left inputs index) (right inputs index))
    (physicalUpper inputs index)
    (Cov.selectedRealConnectedCovarianceConverges
      a covarianceLaws group
      _ (left inputs) (right inputs) index)
    (λ cutoff →
      finitePhysicalCovarianceBelowUpper inputs cutoff index)

literalRealCMP116CoreFinitePhysicalApplicationLevel : ProofLevel
literalRealCMP116CoreFinitePhysicalApplicationLevel = conditional

literalRealCMP116CoreContinuumClusteringCompilerLevel : ProofLevel
literalRealCMP116CoreContinuumClusteringCompilerLevel = machineChecked

literalRealCMP116FinitePhysicalApplicationLevel : ProofLevel
literalRealCMP116FinitePhysicalApplicationLevel = conditional

literalRealCMP116PhysicalRateCalibrationLevel : ProofLevel
literalRealCMP116PhysicalRateCalibrationLevel = conditional

literalRealCMP116ContinuumClusteringCompilerLevel : ProofLevel
literalRealCMP116ContinuumClusteringCompilerLevel = machineChecked

realUpperClosedLimitAuthorityLevel : ProofLevel
realUpperClosedLimitAuthorityLevel = standardImported
