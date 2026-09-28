{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonMarkedSecondJetExpansionExact where

------------------------------------------------------------------------
-- LITERAL TWO-WILSON MARKED SECOND-JET EXPANSION
--
-- The Clay mass-gap consumer needs the mixed source derivative at the
-- normalized base point, not a second copy of the full source-dependent
-- generating functional.  R444 already carries the exact twice-marked CMP116
-- differentiated terms and the signed finite Y-resummation:
--
--   selectedBoundary = sum_Y commonYBoundary(Y)
--
-- with every retained term carrying both selected marks.  R406/R415 prove the
-- pointwise absolute Y-bound, while R448 supplies the source-native
-- domain-specific tree-distance rate split and outer summation.
--
-- This owner packages those facts as the literal Wilson marked *second jet*.
-- It does not identify Balaban's printed bond-valued J with a Wilson loop by
-- fiat; the R444 source construction and the R445 response identification
-- remain the genuine same-object/source payments.
------------------------------------------------------------------------

open import Data.List.Base using (List)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; absℝ; _*ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116CanonicalTwiceMarkedFourStageRound444Exact as R444
import DASHI.Physics.YangMills.BalabanCMP116CanonicalDomainRateSplitRound448Exact as R448
import DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedExpansionRound415Exact as R415
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportConnectionRound411Exact as R411
import DASHI.Physics.YangMills.BalabanCMP116ConnectingOuterSumRound414Exact as R414

record LiteralTwoWilsonMarkedSecondJetExpansion
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base)
    (geometry : R448.CanonicalDomainSpecificRateSplit data)
    : Set₁ where
  field
    -- No new carrier: the literal CMP116 localization domains are the clusters.
    Cluster : Set
    clusterCarrierIsLiteralDomain : Cluster ≡ R444.Domain data

open LiteralTwoWilsonMarkedSecondJetExpansion public

literalSecondJetExpansion :
  ∀ {Measure TestObservable dataSet extension base}
    (data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base)
    (geometry : R448.CanonicalDomainSpecificRateSplit data) →
  LiteralTwoWilsonMarkedSecondJetExpansion data geometry
literalSecondJetExpansion data geometry = record
  { Cluster = R444.Domain data
  ; clusterCarrierIsLiteralDomain = refl
  }

clusters :
  ∀ {Measure TestObservable dataSet extension base}
    {data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base}
    {geometry : R448.CanonicalDomainSpecificRateSplit data} →
  LiteralTwoWilsonMarkedSecondJetExpansion data geometry →
  List (R444.Domain data)
clusters {data = data} expansion =
  R444.localizedDomains data

clusterWeight :
  ∀ {Measure TestObservable dataSet extension base}
    {data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base}
    {geometry : R448.CanonicalDomainSpecificRateSplit data} →
  LiteralTwoWilsonMarkedSecondJetExpansion data geometry →
  R444.Domain data → ℝ
clusterWeight {data = data} expansion =
  R444.commonYBoundaryIntegrand data

clusterMajorant :
  ∀ {Measure TestObservable dataSet extension base}
    {data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base}
    {geometry : R448.CanonicalDomainSpecificRateSplit data} →
  LiteralTwoWilsonMarkedSecondJetExpansion data geometry →
  R444.Domain data → ℝ
clusterMajorant {data = data} expansion =
  R444.commonYShell data

selectedMixedBoundary :
  ∀ {Measure TestObservable dataSet extension base}
    {data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base}
    {geometry : R448.CanonicalDomainSpecificRateSplit data} →
  LiteralTwoWilsonMarkedSecondJetExpansion data geometry →
  ℝ
selectedMixedBoundary {data = data} expansion =
  R444.selectedBoundaryIntegrand data

selectedMixedBoundaryIsClusterSum :
  ∀ {Measure TestObservable dataSet extension base}
    {data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base}
    {geometry : R448.CanonicalDomainSpecificRateSplit data}
    (expansion : LiteralTwoWilsonMarkedSecondJetExpansion data geometry) →
  selectedMixedBoundary expansion
  ≡
  Resum.sumℝ (clusterWeight expansion) (clusters expansion)
selectedMixedBoundaryIsClusterSum {data = data} expansion =
  R444.selectedBoundaryIsCommonYSum data

pointwiseClusterWeightBelowMajorant :
  ∀ {Measure TestObservable dataSet extension base}
    {data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base}
    {geometry : R448.CanonicalDomainSpecificRateSplit data}
    (expansion : LiteralTwoWilsonMarkedSecondJetExpansion data geometry)
    domain →
  absℝ (clusterWeight expansion domain)
  ≤ℝ
  clusterMajorant expansion domain
pointwiseClusterWeightBelowMajorant {data = data} {geometry = geometry}
    expansion domain =
  R415.commonYAbsoluteBoundFromR410
    (R448.preferredR415 data geometry)
    domain

everyClusterConnectsBothWilsonMarks :
  ∀ {Measure TestObservable dataSet extension base}
    {data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base}
    {geometry : R448.CanonicalDomainSpecificRateSplit data}
    (expansion : LiteralTwoWilsonMarkedSecondJetExpansion data geometry)
    domain →
  R411.domainConnectsBothSupports
    (R415.geometry (R448.preferredR415 data geometry))
    domain
everyClusterConnectsBothWilsonMarks {data = data} {geometry = geometry}
    expansion domain =
  R415.everyLocalizedDomainConnects
    (R448.preferredR415 data geometry)
    domain

clusterMajorantSumBelowSourceDecay :
  ∀ {Measure TestObservable dataSet extension base}
    {data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base}
    {geometry : R448.CanonicalDomainSpecificRateSplit data}
    (expansion : LiteralTwoWilsonMarkedSecondJetExpansion data geometry) →
  Resum.sumℝ (clusterMajorant expansion) (clusters expansion)
  ≤ℝ
  R448.sourceAmplitude geometry
    *ℝ
    R414.weight (R448.sourceDecay geometry)
      (R411.selectedConnectingDistance
        (R415.geometry (R448.preferredR415 data geometry)))
clusterMajorantSumBelowSourceDecay {data = data} {geometry = geometry}
    expansion =
  R415.outerShellSumBelowSelectedDecay
    (R448.preferredR415 data geometry)

selectedMixedBoundaryBelowSourceDecay :
  ∀ {Measure TestObservable dataSet extension base}
    {data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base}
    {geometry : R448.CanonicalDomainSpecificRateSplit data}
    (expansion : LiteralTwoWilsonMarkedSecondJetExpansion data geometry) →
  absℝ (selectedMixedBoundary expansion)
  ≤ℝ
  R448.sourceAmplitude geometry
    *ℝ
    R414.weight (R448.sourceDecay geometry)
      (R411.selectedConnectingDistance
        (R415.geometry (R448.preferredR415 data geometry)))
selectedMixedBoundaryBelowSourceDecay {data = data} {geometry = geometry}
    expansion =
  R415.selectedBoundaryBelowSourceDecay
    (R448.preferredR415 data geometry)

literalTwoWilsonMarkedSecondJetCompilerLevel : ProofLevel
literalTwoWilsonMarkedSecondJetCompilerLevel = machineChecked

-- What remains source-native is not another cluster theorem.  It is exactly
-- construction/scalarization of the R444 twice-marked source terms (and the
-- R445 equality tying their total boundary to the literal Wilson mixed
-- response).  Once R444 is inhabited, all four expansion/localization theorems
-- above are compiler output.
literalR444TwiceMarkedTermConstructionLevel : ProofLevel
literalR444TwiceMarkedTermConstructionLevel =
  R444.literalRound444TwiceDifferentiatedTermConstructionAndScalarizationLevel
