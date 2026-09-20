{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116Round406To415Exact where

------------------------------------------------------------------------
-- B / R406 LITERAL EXPANSION -> R415 EXACT R410 EXPANSION
--
-- R406 already carries the selected boundary decomposition, common-Y term
-- lists, common-Y shell and outer sum.  R415 should not ask for those again.
-- The only replay needed between the two presentations is that each R406 term
-- is literally the R410 four-stage differentiated term and that the R406
-- majorant is the canonical R410 marked-product majorant.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _*ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116SelectedTermwiseLocalizationRound406Exact as R406
import DASHI.Physics.YangMills.BalabanCMP116CanonicalPathMarkedReplayRound410Exact as R410
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportConnectionRound411Exact as R411
import DASHI.Physics.YangMills.BalabanCMP116ConnectingOuterSumRound414Exact as R414
import DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedExpansionRound415Exact as R415
import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum
import Data.Rational.Base as ℚ using (ℚ)

record Round406ExactR410Replay
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (application : R406.SelectedCMP116TermwiseLocalization base)
    : Set₁ where
  field
    selectedR410Term :
      R406.Domain application →
      R406.Term application →
      R410.SelectedCMP116PathMarkedTerm (R406.Operator application)

    differentiatedTermIsR410 :
      ∀ domain term →
      R406.differentiatedTerm application domain term
      ≡
      R410.differentiatedTerm (selectedR410Term domain term)

    differentiatedMajorantIsCanonicalR410 :
      ∀ domain term →
      R406.differentiatedTermMajorant application domain term
      ≡
      R415.canonicalTermMajorant (selectedR410Term domain term)

open Round406ExactR410Replay public

record Round406To415Geometry
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (application : R406.SelectedCMP116TermwiseLocalization base)
    : Set₁ where
  field
    geometry :
      R411.SelectedSupportConnectionGeometry
        (R406.Domain application) (R406.Term application)

    decay : R414.AntitoneNonnegativeDecayWeight

    everyLocalizedDomainConnects :
      ∀ domain → R411.domainConnectsBothSupports geometry domain

    domainAmplitude : R406.Domain application → ℝ
    domainAmplitudeNonnegative :
      ∀ domain → 0ℝ ≤ℝ domainAmplitude domain

    commonYShellBelowDomainDecay :
      ∀ domain →
      R406.commonYShell application domain
      ≤ℝ
      domainAmplitude domain
        *ℝ R414.weight decay (R411.domainTreeDistance geometry domain)

    sourceAmplitude : ℝ

    amplitudeSumBelowSourceAmplitude :
      Resum.sumℝ domainAmplitude (R406.localizedDomains application)
      ≤ℝ sourceAmplitude

open Round406To415Geometry public

compileRound415 :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (application : R406.SelectedCMP116TermwiseLocalization base) →
    Round406ExactR410Replay application →
    Round406To415Geometry application →
  R415.SelectedCMP116MarkedExpansion
    (R406.Domain application)
    (R406.Term application)
    (R406.Operator application)
compileRound415 application replay geometryData = record
  { R415.SelectedCMP116MarkedExpansion.localizedDomains =
      R406.localizedDomains application
  ; R415.SelectedCMP116MarkedExpansion.termsWithCommonY =
      R406.termsWithCommonY application
  ; R415.SelectedCMP116MarkedExpansion.selectedTerm =
      selectedR410Term replay
  ; R415.SelectedCMP116MarkedExpansion.commonYBoundaryIntegrand =
      R406.commonYBoundaryIntegrand application
  ; R415.SelectedCMP116MarkedExpansion.commonYShell =
      R406.commonYShell application
  ; R415.SelectedCMP116MarkedExpansion.selectedBoundaryIntegrand =
      R406.selectedBoundaryIntegrand application
  ; R415.SelectedCMP116MarkedExpansion.commonYBoundaryIsSelectedTermSum =
      λ domain →
        let
          sourceEquality = R406.commonYBoundaryIsTermSum application domain
        in
        Resum.sumℝ-cong
          (R406.termsWithCommonY application domain)
          (λ term → differentiatedTermIsR410 replay domain term)
          sourceEquality
  ; R415.SelectedCMP116MarkedExpansion.selectedBoundaryIsCommonYSum =
      R406.selectedBoundaryIsCommonYSum application
  ; R415.SelectedCMP116MarkedExpansion.selectedR410MajorantsBelowCommonYShell =
      λ domain →
        let
          sourceBound =
            R406.differentiatedMajorantsBelowCommonYShell application domain
        in
        Resum.sumℝ-congruent-upper
          (R406.termsWithCommonY application domain)
          (λ term → differentiatedMajorantIsCanonicalR410 replay domain term)
          sourceBound
  ; R415.SelectedCMP116MarkedExpansion.geometry =
      geometry geometryData
  ; R415.SelectedCMP116MarkedExpansion.decay =
      decay geometryData
  ; R415.SelectedCMP116MarkedExpansion.everyLocalizedDomainConnects =
      everyLocalizedDomainConnects geometryData
  ; R415.SelectedCMP116MarkedExpansion.domainAmplitude =
      domainAmplitude geometryData
  ; R415.SelectedCMP116MarkedExpansion.domainAmplitudeNonnegative =
      domainAmplitudeNonnegative geometryData
  ; R415.SelectedCMP116MarkedExpansion.commonYShellBelowDomainDecay =
      commonYShellBelowDomainDecay geometryData
  ; R415.SelectedCMP116MarkedExpansion.sourceAmplitude =
      sourceAmplitude geometryData
  ; R415.SelectedCMP116MarkedExpansion.amplitudeSumBelowSourceAmplitude =
      amplitudeSumBelowSourceAmplitude geometryData
  }

round406To415ExpansionCompilerLevel : ProofLevel
round406To415ExpansionCompilerLevel = machineChecked

-- The exact term replay and the genuine support/counting geometry remain the
-- physical/source inhabitants.  Boundary decomposition is no longer duplicated.
literalRound406ExactR410ReplayLevel : ProofLevel
literalRound406ExactR410ReplayLevel = conditional

literalRound406To415GeometryLevel : ProofLevel
literalRound406To415GeometryLevel = conditional
