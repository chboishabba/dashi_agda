{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116Round406SupportGraphGeometryExact where

------------------------------------------------------------------------
-- B / CONCRETE TWO-MARK SUPPORT GRAPH -> ROUND406/R415 GEOMETRY
--
-- Graph-distance <= tree-edge-count is already compiler-owned.  To prove every
-- retained localization domain connects both selected source supports it is
-- enough to exhibit one surviving selected term in that domain; the concrete
-- support-graph theorem then supplies both mark memberships and the distance
-- lower bound.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116SelectedTermwiseLocalizationRound406Exact as R406
import DASHI.Physics.YangMills.BalabanCMP116Round406To415Exact as R406R415
import DASHI.Physics.YangMills.BalabanCMP116Round406PreferredR415Exact as Preferred406
import DASHI.Physics.YangMills.BalabanCMP116PreferredR415SourceExact as Preferred
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportGraphRound416Exact as Graph
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportConnectionRound411Exact as R411
import DASHI.Physics.YangMills.BalabanCMP116ConnectingOuterSumRound414Exact as R414
import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum

record Round406SupportGraphGeometry
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (application : R406.SelectedCMP116TermwiseLocalization base)
    : Set₁ where
  field
    supportGraph :
      Graph.SelectedTwoMarkSupportGraph
        (R406.Domain application)
        (R406.Term application)

    representativeTerm :
      R406.Domain application → R406.Term application

    representativeSurvives :
      ∀ domain →
      Graph.selectedDifferentiatedTermSurvives supportGraph
        domain (representativeTerm domain)

    decay : R414.AntitoneNonnegativeDecayWeight

    domainAmplitude : R406.Domain application → ℝ
    domainAmplitudeNonnegative :
      ∀ domain → 0ℝ ≤ℝ domainAmplitude domain

    commonYShellBelowDomainDecay :
      ∀ domain →
      R406.commonYShell application domain
      ≤ℝ
      domainAmplitude domain
        *ℝ
        R414.weight decay
          (Graph.domainTreeDistance supportGraph domain)

    sourceAmplitude : ℝ

    amplitudeSumBelowSourceAmplitude :
      Resum.sumℝ domainAmplitude
        (R406.localizedDomains application)
      ≤ℝ sourceAmplitude

open Round406SupportGraphGeometry public

everyDomainConnects :
  ∀ {Measure TestObservable dataSet extension base application}
    (dataSet :
      Round406SupportGraphGeometry
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        application) →
  ∀ domain →
  R411.domainConnectsBothSupports
    (Graph.asR411SelectedSupportConnectionGeometry
      (supportGraph dataSet))
    domain
everyDomainConnects dataSet domain =
  Graph.survivingTermForcesConcreteSupportConnection
    (supportGraph dataSet)
    domain
    (representativeTerm dataSet domain)
    (representativeSurvives dataSet domain)

asRound406To415Geometry :
  ∀ {Measure TestObservable dataSet extension base}
    (application : R406.SelectedCMP116TermwiseLocalization base) →
  Round406SupportGraphGeometry
    {Measure = Measure} {TestObservable = TestObservable}
    {dataSet = dataSet} {extension = extension} {base = base}
    application →
  R406R415.Round406To415Geometry application
asRound406To415Geometry application dataSet = record
  { R406R415.Round406To415Geometry.geometry =
      Graph.asR411SelectedSupportConnectionGeometry
        (supportGraph dataSet)
  ; R406R415.Round406To415Geometry.decay =
      decay dataSet
  ; R406R415.Round406To415Geometry.everyLocalizedDomainConnects =
      everyDomainConnects dataSet
  ; R406R415.Round406To415Geometry.domainAmplitude =
      domainAmplitude dataSet
  ; R406R415.Round406To415Geometry.domainAmplitudeNonnegative =
      domainAmplitudeNonnegative dataSet
  ; R406R415.Round406To415Geometry.commonYShellBelowDomainDecay =
      commonYShellBelowDomainDecay dataSet
  ; R406R415.Round406To415Geometry.sourceAmplitude =
      sourceAmplitude dataSet
  ; R406R415.Round406To415Geometry.amplitudeSumBelowSourceAmplitude =
      amplitudeSumBelowSourceAmplitude dataSet
  }

round406SupportGraphGeometryCompilerLevel : ProofLevel
round406SupportGraphGeometryCompilerLevel = machineChecked

-- Remaining B geometry/source facts:
-- * selected support distance and domain tree metric attach to the concrete
--   support graph;
-- * every retained domain has a surviving twice-marked term containing both
--   selected source links;
-- * per-domain shell amplitudes obey the source tree-decay/summability bound.
literalRound406SupportGraphAndAmplitudeLevel : ProofLevel
literalRound406SupportGraphAndAmplitudeLevel = conditional


compilePreferredFromSupportGraph :
  ∀ {Measure TestObservable dataSet extension base}
    (application : R406.SelectedCMP116TermwiseLocalization base)
    (replay : R406R415.Round406ExactR410Replay application)
    (geometryData :
      Round406SupportGraphGeometry
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        application) →
  Preferred.PreferredR415Source
    (R406.Domain application)
    (R406.Term application)
    (R406.Operator application)
compilePreferredFromSupportGraph application replay geometryData =
  Preferred406.compilePreferredFromRound406
    application replay
    (asRound406To415Geometry application geometryData)

round406SupportGraphToPreferredR415CompilerLevel : ProofLevel
round406SupportGraphToPreferredR415CompilerLevel = machineChecked
