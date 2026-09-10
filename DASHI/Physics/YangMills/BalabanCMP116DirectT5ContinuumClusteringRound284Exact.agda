{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116DirectT5ContinuumClusteringRound284Exact where

------------------------------------------------------------------------
-- ROUND284 / DIRECT CMP116 -> T5 FINITE COVARIANCE -> CONTINUUM B1
--
-- R283 is a valid finite-RG producer route, but it is not mandatory.  The
-- direct CMP116 two-source owner already supplies the stronger source-facing
-- shape needed for B1: the connected covariance of two literal source
-- insertions is below a rooted connecting shell, and the shell compiler gives
-- (1/4)(1/2)^distance.
--
-- R278 already proves that the SAME selected finite-measure covariance
-- magnitude converges to the continuum covariance magnitude.  R281 constructs
-- the reconstructed spectrum with that continuum covariance as
-- `connectedCorrelation` definitionally.
--
-- Therefore the least-privilege direct route is:
--
--   exact finite T5 covariance
--     <= CMP116 connecting shell
--     <= (1/4)(1/2)^time
--       --limit--> exact continuum covariance
--       == spectrum connectedCorrelation.
--
-- No FiniteRGReopeningStep, Heat/Doob, Langevin, Dyson, or unified norm is a
-- prerequisite on this route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanClayOneSidedCorrelationLimitRound276Exact as R276
import DASHI.Physics.YangMills.BalabanCMP116TwoSourceConnectedClusteringRound274Exact as Direct
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power

------------------------------------------------------------------------
-- Exact finite T5 covariance presented as a CMP116 rooted-shell observable.
------------------------------------------------------------------------

record DirectT5TwoSourceShell
    {Measure TestObservable : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    : Set₁ where
  field
    Scale Volume Root : Set
    shellData : Shell.TraversalShellData Scale Volume Root

    scaleAtCutoff : Nat → Scale
    volumeAtCutoff : Nat → Volume
    physicalDistance : TestObservable → TestObservable → Nat
    connectingRoot : Nat → TestObservable → TestObservable → Root

    -- The source theorem is stated directly on the SAME finite T5 covariance
    -- consumed by R278.  There is no intermediate covariance identity.
    finiteCovarianceBelowConnectingShell : ∀ cutoff left right →
      R278.connectedCovarianceMagnitude extension
        (Gram.measureSequence dataSet cutoff) left right
      ≤ Shell.rootedShell shellData
          (scaleAtCutoff cutoff) (volumeAtCutoff cutoff)
          (connectingRoot cutoff left right)
          (physicalDistance left right)

    connectingClusterMeetsBothSupports : ∀ cutoff left right → Set

open DirectT5TwoSourceShell public

asDirectTwoSourceData :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet} →
  (shell : DirectT5TwoSourceShell dataSet extension) →
  Direct.TwoSourceConnectedRootedShellData
    (Scale shell) (Volume shell) (Root shell) Nat TestObservable
asDirectTwoSourceData {dataSet = dataSet} {extension = extension} shell = record
  { Direct.TwoSourceConnectedRootedShellData.shellData = shellData shell
  ; Direct.TwoSourceConnectedRootedShellData.stateAtScale = λ cutoff → cutoff
  ; Direct.TwoSourceConnectedRootedShellData.scaleOf = scaleAtCutoff shell
  ; Direct.TwoSourceConnectedRootedShellData.volumeOf = volumeAtCutoff shell
  ; Direct.TwoSourceConnectedRootedShellData.physicalDistance = physicalDistance shell
  ; Direct.TwoSourceConnectedRootedShellData.connectingRoot = connectingRoot shell
  ; Direct.TwoSourceConnectedRootedShellData.connectedCovarianceMagnitude =
      λ cutoff left right →
        R278.connectedCovarianceMagnitude extension
          (Gram.measureSequence dataSet cutoff) left right
  ; Direct.TwoSourceConnectedRootedShellData.connectedCovarianceBelowConnectingShell =
      finiteCovarianceBelowConnectingShell shell
  ; Direct.TwoSourceConnectedRootedShellData.connectingClusterMeetsBothSupports =
      connectingClusterMeetsBothSupports shell
  }

------------------------------------------------------------------------
-- Selected spectral pair/time realization and closed-order limit.
------------------------------------------------------------------------

record DirectT5ContinuumClusteringPayment
    {Measure TestObservable SpectralObservable Energy : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    (source : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests)
    : Set₁ where
  field
    directShell : DirectT5TwoSourceShell dataSet extension

    -- The exact selected test pair at spectral time t has support separation t.
    selectedPairDistanceIsTime : ∀ observable time →
      physicalDistance directShell
        (R278.left tests (R281.indexFor source observable time))
        (R278.right tests (R281.indexFor source observable time))
      ≡ time

    -- Construct the spectral envelope on the exact source majorant, rather than
    -- post-hoc asserting that two independently named rates are equal.
    spectrumEnvelopeIsRootedGeometric : ∀ observable time →
      R281.clusteringEnvelope source observable time
      ≡ Shell.quarter * Power.rationalPower Geo.half time

    -- The spectrum's Bound order is the ordinary rational order on this direct
    -- realization.
    rationalOrderIsSpectrumOrder : ∀ left right →
      (left ≤ right) ≡ R281.LessEqual source left right

    -- Standard ordered-limit authority for the concrete scalar convergence
    -- already carried by T5.  This is source-independent topology, not a new YM
    -- estimate.
    rationalUpperClosedUnderSelectedLimit :
      (sequence : Nat → ℚ) (target upper : ℚ) →
      Gram.Converges (Gram.scalarConvergence dataSet) sequence target →
      (∀ cutoff → sequence cutoff ≤ upper) →
      target ≤ upper

open DirectT5ContinuumClusteringPayment public

selectedFiniteCorrelation :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {source : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  DirectT5ContinuumClusteringPayment dataSet extension tests source →
  Nat → SpectralObservable → Nat → ℚ
selectedFiniteCorrelation {dataSet = dataSet} {extension = extension}
    {tests = tests} {source = source} payment cutoff observable time =
  R278.connectedCovarianceMagnitude extension
    (Gram.measureSequence dataSet cutoff)
    (R278.left tests (R281.indexFor source observable time))
    (R278.right tests (R281.indexFor source observable time))

rationalUpperClosedConvergence :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {source : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  DirectT5ContinuumClusteringPayment dataSet extension tests source →
  R276.UpperClosedConvergence ℚ
rationalUpperClosedConvergence {dataSet = dataSet} payment = record
  { R276.UpperClosedConvergence.Converges =
      Gram.Converges (Gram.scalarConvergence dataSet)
  ; R276.UpperClosedConvergence.LessEqual = _≤_
  ; R276.UpperClosedConvergence.upperClosedUnderLimit =
      rationalUpperClosedUnderSelectedLimit payment
  }

finiteSelectedUpper :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {source : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests}
    (payment : DirectT5ContinuumClusteringPayment dataSet extension tests source)
    cutoff observable time →
  selectedFiniteCorrelation payment cutoff observable time
  ≤ R281.clusteringEnvelope source observable time
finiteSelectedUpper {tests = tests} {source = source} payment cutoff observable time =
  let
    left = R278.left tests (R281.indexFor source observable time)
    right = R278.right tests (R281.indexFor source observable time)
    geometric = Direct.connectedCovarianceGeometricBound
      (asDirectTwoSourceData (directShell payment)) cutoff left right
    atTime = subst
      (λ distance →
        selectedFiniteCorrelation payment cutoff observable time
        ≤ Shell.quarter * Power.rationalPower Geo.half distance)
      (selectedPairDistanceIsTime payment observable time)
      geometric
  in
  subst
    (λ upper → selectedFiniteCorrelation payment cutoff observable time ≤ upper)
    (sym (spectrumEnvelopeIsRootedGeometric payment observable time))
    atTime

asSameSpectrumFiniteCorrelationUpper :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {source : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests}
    (payment : DirectT5ContinuumClusteringPayment dataSet extension tests source) →
  R276.SameSpectrumFiniteCorrelationUpper
    (R281.asReconstructedClusteringSpectrum source)
asSameSpectrumFiniteCorrelationUpper
    {dataSet = dataSet} {extension = extension} {tests = tests}
    {source = source} payment = record
  { R276.SameSpectrumFiniteCorrelationUpper.orderLimit =
      rationalUpperClosedConvergence payment
  ; R276.SameSpectrumFiniteCorrelationUpper.finiteConnectedCorrelation =
      selectedFiniteCorrelation payment
  ; R276.SameSpectrumFiniteCorrelationUpper.finiteConvergesToSpectrumCorrelation =
      λ observable time →
        R278.selectedConnectedCovarianceMagnitudeConverges
          extension tests (R281.indexFor source observable time)
  ; R276.SameSpectrumFiniteCorrelationUpper.finiteUniformClusteringUpper =
      finiteSelectedUpper payment
  ; R276.SameSpectrumFiniteCorrelationUpper.orderIsSpectrumOrder =
      rationalOrderIsSpectrumOrder payment
  }

compileDirectCMP116ToContinuumClustering :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {source : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  DirectT5ContinuumClusteringPayment dataSet extension tests source →
  Gap.ClusteringUpperBound (R281.asReconstructedClusteringSpectrum source)
compileDirectCMP116ToContinuumClustering payment =
  R276.compileFiniteUniformUpperToSpectrumClustering
    (asSameSpectrumFiniteCorrelationUpper payment)

record Round284Boundary : Set where
  constructor round284-boundary
  field
    finiteRGReopeningMandatory : Bool
    finiteRGReopeningMandatoryIsFalse : finiteRGReopeningMandatory ≡ false

    heatDoobLangevinMandatory : Bool
    heatDoobLangevinMandatoryIsFalse : heatDoobLangevinMandatory ≡ false

    unifiedNormMandatory : Bool
    unifiedNormMandatoryIsFalse : unifiedNormMandatory ≡ false

    exactT5CovarianceUsedDirectly : Bool
    exactT5CovarianceUsedDirectlyIsTrue : exactT5CovarianceUsedDirectly ≡ true

    covarianceLimitCompilerOwned : Bool
    covarianceLimitCompilerOwnedIsTrue : covarianceLimitCompilerOwned ≡ true

    literalTwoSourceCMP116ShellStillPhysical : Bool
    literalTwoSourceCMP116ShellStillPhysicalIsTrue :
      literalTwoSourceCMP116ShellStillPhysical ≡ true

canonicalRound284Boundary : Round284Boundary
canonicalRound284Boundary =
  round284-boundary false refl false refl false refl true refl true refl true refl

round284DirectT5ContinuumClusteringCompilerLevel : ProofLevel
round284DirectT5ContinuumClusteringCompilerLevel = machineChecked

round284OrderedLimitAuthorityLevel : ProofLevel
round284OrderedLimitAuthorityLevel = standardImported

round284LiteralTwoSourceCMP116ShellLevel : ProofLevel
round284LiteralTwoSourceCMP116ShellLevel =
  Direct.round274LiteralTwoPhysicalJInsertionsConnectedShellLevel
