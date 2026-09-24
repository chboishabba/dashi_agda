{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalDomainRateSplitRound448Exact where

------------------------------------------------------------------------
-- B / ROUND448: R444 + DOMAIN-SPECIFIC CMP116 d_k(Y) -> PREFERRED R415.
--
-- This is the source-faithful replacement for the legacy R416/R435 path.
--
-- CMP116 (1.26)--(1.29) supplies a domain-dependent sourceTreeDistance(Y).
-- R444 supplies structurally twice-marked, nonempty retained fibres.
-- R447 needs only the physical connected-core inequality
--
--   graphDist(leftMark,rightMark) <= sourceTreeDistance(Y).
--
-- Once that inequality is supplied, the source rate split itself constructs
-- the per-domain amplitudes and their outer sum.  Thus B5 is compiler-owned on
-- this preferred path, with no global ymTreeEdgeCount identification.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Membership.Propositional using (_∈_)
import Data.Nat.Base as Nat
open import Data.Product using (Σ; _×_; _,_)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _≤ℝ_; absℝ; ≤ℝ-refl; ≤ℝ-trans; mulZeroʳ; *-assoc; mulMonotoneNonnegative)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.YangMills.YMSupportGraphDistance as Graph
import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanCMP116CanonicalTwiceMarkedSupportRound434Exact as R434
import DASHI.Physics.YangMills.BalabanCMP116CanonicalTwiceMarkedFourStageRound444Exact as R444
import DASHI.Physics.YangMills.BalabanCMP116CanonicalFourStageR406Round429Exact as R429
import DASHI.Physics.YangMills.BalabanCMP116SelectedTermwiseLocalizationRound406Exact as R406
import DASHI.Physics.YangMills.BalabanCMP116DomainSpecificSupportGeometryRound447Exact as R447
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportConnectionRound411Exact as R411
import DASHI.Physics.YangMills.BalabanCMP116ConnectingOuterSumRound414Exact as R414
import DASHI.Physics.YangMills.BalabanCMP116Round406To415Exact as R406R415
import DASHI.Physics.YangMills.BalabanCMP116Round406ExactR410ReplayRound421Exact as R421
import DASHI.Physics.YangMills.BalabanCMP116Round406PreferredR415Exact as Preferred406
import DASHI.Physics.YangMills.BalabanCMP116PreferredR415SourceExact as Preferred
import DASHI.Physics.YangMills.BalabanCMP116Round406SourceRateSplitAmplitudeRound420Exact as R420

record CanonicalDomainSpecificRateSplit
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base)
    : Set₁ where
  field
    -- This is now the complete live B4 support/tree geometry.
    sourceTreeDistanceDominatesSelectedGraphDistance :
      ∀ domain →
      Graph.ymGraphDist (R444.leftMark data) (R444.rightMark data)
      Nat.≤
      Source.sourceTreeDistance (R444.source data) domain

open CanonicalDomainSpecificRateSplit public

containsSelectedLink :
  ∀ {Measure TestObservable dataSet extension base data} →
  CanonicalDomainSpecificRateSplit
    {Measure = Measure} {TestObservable = TestObservable}
    {dataSet = dataSet} {extension = extension} {base = base}
    data →
  R444.Domain data → Support.Link → Set
containsSelectedLink {data = data} geometry domain link =
  Σ (R444.Term data)
    (λ term →
      term ∈ R444.termsWithCommonY data domain
      × R444.CarriesLink data (R434.rawTerm term) link)

domainGeometry :
  ∀ {Measure TestObservable dataSet extension base data} →
  (geometry :
    CanonicalDomainSpecificRateSplit
      {Measure = Measure} {TestObservable = TestObservable}
      {dataSet = dataSet} {extension = extension} {base = base}
      data) →
  R447.DomainSpecificTwoMarkSupportGeometry
    (R444.Domain data) (R444.Term data)
domainGeometry {data = data} geometry = record
  { R447.DomainSpecificTwoMarkSupportGeometry.leftMark =
      R444.leftMark data
  ; R447.DomainSpecificTwoMarkSupportGeometry.rightMark =
      R444.rightMark data
  ; R447.DomainSpecificTwoMarkSupportGeometry.domainTreeDistance =
      Source.sourceTreeDistance (R444.source data)
  ; R447.DomainSpecificTwoMarkSupportGeometry.containsSelectedLink =
      containsSelectedLink geometry
  ; R447.DomainSpecificTwoMarkSupportGeometry.selectedDifferentiatedTermSurvives =
      λ domain term → term ∈ R444.termsWithCommonY data domain
  ; R447.DomainSpecificTwoMarkSupportGeometry.survivingTermContainsLeftMark =
      λ domain term membership →
        term , (membership , R434.carriesLeft term)
  ; R447.DomainSpecificTwoMarkSupportGeometry.survivingTermContainsRightMark =
      λ domain term membership →
        term , (membership , R434.carriesRight term)
  ; R447.DomainSpecificTwoMarkSupportGeometry.connectedDomainTreeDominatesSupportGraphDistance =
      λ domain left right →
        sourceTreeDistanceDominatesSelectedGraphDistance geometry domain
  }

everyDomainConnects :
  ∀ {Measure TestObservable dataSet extension base data}
    (geometry :
      CanonicalDomainSpecificRateSplit
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        data) →
  ∀ domain →
  R411.domainConnectsBothSupports
    (R447.asR411SelectedSupportConnectionGeometry (domainGeometry geometry))
    domain
everyDomainConnects {data = data} geometry domain =
  R447.survivingTermForcesConnection
    (domainGeometry geometry)
    domain
    (R444.selectedHead data domain)
    (R444.selectedHeadBelongs data domain)

sourceDecay :
  ∀ {Measure TestObservable dataSet extension base data} →
  CanonicalDomainSpecificRateSplit
    {Measure = Measure} {TestObservable = TestObservable}
    {dataSet = dataSet} {extension = extension} {base = base}
    data →
  R414.AntitoneNonnegativeDecayWeight
sourceDecay {data = data} geometry = record
  { R414.AntitoneNonnegativeDecayWeight.weight =
      Source.residualDecayWeight (R444.source data)
  ; R414.AntitoneNonnegativeDecayWeight.weightNonnegative =
      Source.residualDecayWeightNonnegative (R444.source data)
  ; R414.AntitoneNonnegativeDecayWeight.weightAntitone =
      Source.residualDecayWeightAntitone (R444.source data)
  }

domainAmplitude :
  ∀ {Measure TestObservable dataSet extension base data} →
  CanonicalDomainSpecificRateSplit
    {Measure = Measure} {TestObservable = TestObservable}
    {dataSet = dataSet} {extension = extension} {base = base}
    data →
  R444.Domain data → ℝ
domainAmplitude {data = data} geometry domain =
  Source.sourcePrefactor (R444.source data) *ℝ
  Source.entropyHalfWeight (R444.source data)
    (Source.sourceTreeDistance (R444.source data) domain)

sourceAmplitude :
  ∀ {Measure TestObservable dataSet extension base data} →
  CanonicalDomainSpecificRateSplit
    {Measure = Measure} {TestObservable = TestObservable}
    {dataSet = dataSet} {extension = extension} {base = base}
    data →
  ℝ
sourceAmplitude {data = data} geometry =
  Source.sourcePrefactor (R444.source data) *ℝ
  Source.entropyAllowance (R444.source data)

domainAmplitudeNonnegative :
  ∀ {Measure TestObservable dataSet extension base data}
    (geometry :
      CanonicalDomainSpecificRateSplit
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        data) →
  ∀ domain →
  0ℝ ≤ℝ domainAmplitude geometry domain
domainAmplitudeNonnegative {data = data} geometry domain =
  subst
    (λ lower → lower ≤ℝ domainAmplitude geometry domain)
    (mulZeroʳ 0ℝ)
    (mulMonotoneNonnegative
      ≤ℝ-refl
      (Source.sourcePrefactorNonnegative (R444.source data))
      ≤ℝ-refl
      (Source.entropyHalfWeightNonnegative (R444.source data)
        (Source.sourceTreeDistance (R444.source data) domain)))

commonYShellBelowDomainDecay :
  ∀ {Measure TestObservable dataSet extension base data}
    (geometry :
      CanonicalDomainSpecificRateSplit
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        data) →
  ∀ domain →
  R444.commonYShell data domain
  ≤ℝ
  domainAmplitude geometry domain
    *ℝ
    R414.weight (sourceDecay geometry)
      (Source.sourceTreeDistance (R444.source data) domain)
commonYShellBelowDomainDecay {data = data} geometry domain =
  let
    src = R444.source data
    sourceBound =
      Source.fixedYEquation129RateSplit src domain
    leftTransport =
      subst
        (λ left →
          left ≤ℝ
          Source.sourcePrefactor src *ℝ
            (Source.entropyHalfWeight src
              (Source.sourceTreeDistance src domain)
            *ℝ
            Source.residualDecayWeight src
              (Source.sourceTreeDistance src domain)))
        (R444.sourceFixedYShellIsLiteralCommonYShell data domain)
        sourceBound
  in
  subst
    (λ upper → R444.commonYShell data domain ≤ℝ upper)
    (sym
      (*-assoc
        (Source.sourcePrefactor src)
        (Source.entropyHalfWeight src
          (Source.sourceTreeDistance src domain))
        (Source.residualDecayWeight src
          (Source.sourceTreeDistance src domain))))
    leftTransport

amplitudeSumBelowSourceAmplitude :
  ∀ {Measure TestObservable dataSet extension base data}
    (geometry :
      CanonicalDomainSpecificRateSplit
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        data) →
  Resum.sumℝ (domainAmplitude geometry) (R444.localizedDomains data)
  ≤ℝ sourceAmplitude geometry
amplitudeSumBelowSourceAmplitude {data = data} geometry =
  let
    src = R444.source data
    halfWeight =
      λ domain →
        Source.entropyHalfWeight src (Source.sourceTreeDistance src domain)

    budgetOnLiteralDomains :
      Resum.sumℝ halfWeight (R444.localizedDomains data)
      ≤ℝ Source.entropyAllowance src
    budgetOnLiteralDomains =
      subst
        (λ domains →
          Resum.sumℝ halfWeight domains ≤ℝ Source.entropyAllowance src)
        (R444.sourceDomainsAreLiteralDomains data)
        (Source.equation126128WeightedFibreBudget src)

    halfWeightSumNonnegative :
      0ℝ ≤ℝ Resum.sumℝ halfWeight (R444.localizedDomains data)
    halfWeightSumNonnegative =
      R420.sumNonnegative
        halfWeight
        (R444.localizedDomains data)
        (λ domain →
          Source.entropyHalfWeightNonnegative src
            (Source.sourceTreeDistance src domain))

    scaledBudget :
      Source.sourcePrefactor src *ℝ
        Resum.sumℝ halfWeight (R444.localizedDomains data)
      ≤ℝ
      Source.sourcePrefactor src *ℝ Source.entropyAllowance src
    scaledBudget =
      mulMonotoneNonnegative
        (Source.sourcePrefactorNonnegative src)
        ≤ℝ-refl
        halfWeightSumNonnegative
        budgetOnLiteralDomains

    factored =
      R420.scaleFiniteSum
        (Source.sourcePrefactor src)
        halfWeight
        (R444.localizedDomains data)
  in
  subst
    (λ left → left ≤ℝ sourceAmplitude geometry)
    factored
    scaledBudget

sourceAmplitudeNonnegative :
  ∀ {Measure TestObservable dataSet extension base data}
    (geometry :
      CanonicalDomainSpecificRateSplit
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        data) →
  0ℝ ≤ℝ sourceAmplitude geometry
sourceAmplitudeNonnegative {data = data} geometry =
  let
    src = R444.source data
    halfWeight =
      λ domain →
        Source.entropyHalfWeight src (Source.sourceTreeDistance src domain)

    sumNN :
      0ℝ ≤ℝ Resum.sumℝ halfWeight (Source.localizedDomains src)
    sumNN =
      R420.sumNonnegative
        halfWeight
        (Source.localizedDomains src)
        (λ domain →
          Source.entropyHalfWeightNonnegative src
            (Source.sourceTreeDistance src domain))

    allowanceNN : 0ℝ ≤ℝ Source.entropyAllowance src
    allowanceNN =
      ≤ℝ-trans sumNN (Source.equation126128WeightedFibreBudget src)
  in
  subst
    (λ lower → lower ≤ℝ sourceAmplitude geometry)
    (mulZeroʳ 0ℝ)
    (mulMonotoneNonnegative
      ≤ℝ-refl
      (Source.sourcePrefactorNonnegative src)
      ≤ℝ-refl
      allowanceNN)

asRound406Geometry :
  ∀ {Measure TestObservable dataSet extension base}
    (data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base)
    (geometry : CanonicalDomainSpecificRateSplit data) →
  R406R415.Round406To415Geometry
    (R429.canonicalApplication (R444.asR429 data))
asRound406Geometry data geometry = record
  { R406R415.Round406To415Geometry.geometry =
      R447.asR411SelectedSupportConnectionGeometry (domainGeometry geometry)
  ; R406R415.Round406To415Geometry.decay = sourceDecay geometry
  ; R406R415.Round406To415Geometry.everyLocalizedDomainConnects =
      everyDomainConnects geometry
  ; R406R415.Round406To415Geometry.domainAmplitude =
      domainAmplitude geometry
  ; R406R415.Round406To415Geometry.domainAmplitudeNonnegative =
      domainAmplitudeNonnegative geometry
  ; R406R415.Round406To415Geometry.commonYShellBelowDomainDecay =
      commonYShellBelowDomainDecay geometry
  ; R406R415.Round406To415Geometry.sourceAmplitude =
      sourceAmplitude geometry
  ; R406R415.Round406To415Geometry.amplitudeSumBelowSourceAmplitude =
      amplitudeSumBelowSourceAmplitude geometry
  }

preferredR415 :
  ∀ {Measure TestObservable dataSet extension base}
    (data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base)
    (geometry : CanonicalDomainSpecificRateSplit data) →
  Preferred.PreferredR415Source
    (R444.Domain data)
    (R444.Term data)
    (R444.Operator data)
preferredR415 data geometry =
  let
    fourStage = R444.asR429 data
    application = R429.canonicalApplication fourStage
    replay =
      R421.compileExactR410Replay application
        (R429.canonicalOperatorReplay fourStage)
  in
  Preferred406.compilePreferredFromRound406
    application replay (asRound406Geometry data geometry)

selectedBoundaryBelowSourceDecay :
  ∀ {Measure TestObservable dataSet extension base}
    (data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base)
    (geometry : CanonicalDomainSpecificRateSplit data) →
  absℝ (R444.selectedBoundaryIntegrand data)
  ≤ℝ
  sourceAmplitude geometry *ℝ
    R414.weight (sourceDecay geometry)
      (Graph.ymGraphDist (R444.leftMark data) (R444.rightMark data))
selectedBoundaryBelowSourceDecay data geometry =
  Preferred.preferredR415SelectedBoundaryDecay
    (preferredR415 data geometry)

round448DomainSpecificRateSplitCompilerLevel : ProofLevel
round448DomainSpecificRateSplitCompilerLevel = machineChecked

round448OuterAmplitudeB5CompilerLevel : ProofLevel
round448OuterAmplitudeB5CompilerLevel = machineChecked

-- Preferred B4 is now only the source/physical connected-core geometry
-- graphDist(left,right) <= d_k(Y).  B5 then follows from the published
-- (1.26)--(1.29) weighted-fibre budget and finite ordered-real algebra.
literalRound448ConnectedCoreDistanceLevel : ProofLevel
literalRound448ConnectedCoreDistanceLevel = conditional
