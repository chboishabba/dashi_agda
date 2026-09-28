{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonCMP116MarkedExpansionExact where

------------------------------------------------------------------------
-- DIRECT LITERAL TWO-WILSON CMP116 MARKED EXPANSION
--
-- Least-privilege source surface for W1/W3.
--
-- Each literal differentiated term carries an R413 source-shaped CMP99
-- path-derivative replay.  R413 fixes the changed stage definitionally to the
-- path/background derivative; R410 then supplies the canonical noncommutative
-- four-stage marked product bound.  The source must still prove:
--
--   * the literal differentiated scalar is that canonical product difference;
--   * the two finite source-resummation equalities;
--   * the fixed-Y canonical-majorant sum;
--   * concrete two-mark support geometry and the source rate split.
--
-- No R406 record, arbitrary changed-stage choice, or post-hoc printed-J=Wilson
-- equality is required by this constructor.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; absℝ; _*ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum
import DASHI.Physics.YangMills.BalabanCMP109FourStageOperatorFactorRound407Exact as R407
import DASHI.Physics.YangMills.BalabanCMP99MarkedStageDifferenceRound408Exact as R408
import DASHI.Physics.YangMills.BalabanNoncommutativeMarkedOperatorProductExact as Marked
import DASHI.Physics.YangMills.BalabanCMP116CanonicalPathMarkedReplayRound410Exact as R410
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportConnectionRound411Exact as R411
import DASHI.Physics.YangMills.BalabanCMP116ConnectingOuterSumRound414Exact as R414
import DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedExpansionRound415Exact as R415
import DASHI.Physics.YangMills.BalabanCMP99PathDerivativeSourceReplayRound413Exact as R413


selectedTermFromR413 :
  ∀ {Operator}
    (replaySource : R413.CMP99PathDerivativeSourceReplay Operator ℝ)
    (value : ℝ) →
  (let replay = R413.asR410CanonicalPathReplay replaySource in
   absℝ value
   ≡
   Marked.operatorNorm
     (R408.telescopeAlgebra (R410.stageDifference replay))
     (Marked.difference
       (R408.telescopeAlgebra (R410.stageDifference replay))
       (Marked.operatorProduct
         (R408.telescopeAlgebra (R410.stageDifference replay))
         (R407.stageOperator
           (R407.before (R408.ordinaryPair (R410.stageDifference replay))))
         R407.cmp109DerivativeStages)
       (Marked.operatorProduct
         (R408.telescopeAlgebra (R410.stageDifference replay))
         (R407.stageOperator
           (R407.after (R408.ordinaryPair (R410.stageDifference replay))))
         R407.cmp109DerivativeStages))) →
  R410.SelectedCMP116PathMarkedTerm Operator
selectedTermFromR413 replaySource value scalarization = record
  { R410.SelectedCMP116PathMarkedTerm.replay =
      R413.asR410CanonicalPathReplay replaySource
  ; R410.SelectedCMP116PathMarkedTerm.differentiatedTerm =
      value
  ; R410.SelectedCMP116PathMarkedTerm.differentiatedTermAbsoluteIsCanonicalProductDifferenceNorm =
      scalarization
  }

record LiteralTwoWilsonCMP116MarkedExpansionSource
    (Domain Term Operator : Set) : Set₁ where
  field
    localizedDomains : List Domain
    termsWithCommonY : Domain → List Term

    sourceReplay :
      Domain → Term → R413.CMP99PathDerivativeSourceReplay Operator ℝ

    differentiatedTerm : Domain → Term → ℝ

    differentiatedTermScalarization :
      ∀ domain term →
      let replay = R413.asR410CanonicalPathReplay (sourceReplay domain term)
      in
      absℝ (differentiatedTerm domain term)
      ≡
      Marked.operatorNorm
        (R408.telescopeAlgebra (R410.stageDifference replay))
        (Marked.difference
          (R408.telescopeAlgebra (R410.stageDifference replay))
          (Marked.operatorProduct
            (R408.telescopeAlgebra (R410.stageDifference replay))
            (R407.stageOperator
              (R407.before (R408.ordinaryPair (R410.stageDifference replay))))
            R407.cmp109DerivativeStages)
          (Marked.operatorProduct
            (R408.telescopeAlgebra (R410.stageDifference replay))
            (R407.stageOperator
              (R407.after (R408.ordinaryPair (R410.stageDifference replay))))
            R407.cmp109DerivativeStages))

    commonYBoundaryIntegrand commonYShell : Domain → ℝ
    selectedBoundaryIntegrand : ℝ

    commonYBoundaryIsTermSum :
      ∀ domain →
      commonYBoundaryIntegrand domain
      ≡
      Resum.sumℝ
        (differentiatedTerm domain)
        (termsWithCommonY domain)

    selectedBoundaryIsCommonYSum :
      selectedBoundaryIntegrand
      ≡ Resum.sumℝ commonYBoundaryIntegrand localizedDomains

    geometry : R411.SelectedSupportConnectionGeometry Domain Term

    everyLocalizedDomainConnects :
      ∀ domain → R411.domainConnectsBothSupports geometry domain

    decay : R414.AntitoneNonnegativeDecayWeight

    domainAmplitude : Domain → ℝ
    domainAmplitudeNonnegative :
      ∀ domain → 0ℝ ≤ℝ domainAmplitude domain

    commonYShellBelowDomainDecay :
      ∀ domain →
      commonYShell domain
      ≤ℝ
      domainAmplitude domain
        *ℝ R414.weight decay
          (R411.domainTreeDistance geometry domain)

    sourceAmplitude : ℝ

    amplitudeSumBelowSourceAmplitude :
      Resum.sumℝ domainAmplitude localizedDomains
      ≤ℝ sourceAmplitude

    -- Literal CMP116 (1.23)--(1.29) fixed-Y payment after R413/R410.
    canonicalMajorantsBelowCommonYShell :
      ∀ domain →
      Resum.sumℝ
        (λ term →
          R415.canonicalTermMajorant
            (selectedTermFromR413
              (sourceReplay domain term)
              (differentiatedTerm domain term)
              (differentiatedTermScalarization domain term)))
        (termsWithCommonY domain)
      ≤ℝ commonYShell domain

  selectedTerm :
    Domain → Term → R410.SelectedCMP116PathMarkedTerm Operator
  selectedTerm domain term =
    selectedTermFromR413
      (sourceReplay domain term)
      (differentiatedTerm domain term)
      (differentiatedTermScalarization domain term)

open LiteralTwoWilsonCMP116MarkedExpansionSource public

asR415 :
  ∀ {Domain Term Operator} →
  LiteralTwoWilsonCMP116MarkedExpansionSource Domain Term Operator →
  R415.SelectedCMP116MarkedExpansion Domain Term Operator
asR415 source = record
  { R415.SelectedCMP116MarkedExpansion.localizedDomains =
      localizedDomains source
  ; R415.SelectedCMP116MarkedExpansion.termsWithCommonY =
      termsWithCommonY source
  ; R415.SelectedCMP116MarkedExpansion.selectedTerm =
      selectedTerm source
  ; R415.SelectedCMP116MarkedExpansion.commonYBoundaryIntegrand =
      commonYBoundaryIntegrand source
  ; R415.SelectedCMP116MarkedExpansion.commonYShell =
      commonYShell source
  ; R415.SelectedCMP116MarkedExpansion.selectedBoundaryIntegrand =
      selectedBoundaryIntegrand source
  ; R415.SelectedCMP116MarkedExpansion.commonYBoundaryIsSelectedTermSum =
      commonYBoundaryIsTermSum source
  ; R415.SelectedCMP116MarkedExpansion.selectedBoundaryIsCommonYSum =
      selectedBoundaryIsCommonYSum source
  ; R415.SelectedCMP116MarkedExpansion.selectedR410MajorantsBelowCommonYShell =
      canonicalMajorantsBelowCommonYShell source
  ; R415.SelectedCMP116MarkedExpansion.geometry =
      geometry source
  ; R415.SelectedCMP116MarkedExpansion.decay =
      decay source
  ; R415.SelectedCMP116MarkedExpansion.everyLocalizedDomainConnects =
      everyLocalizedDomainConnects source
  ; R415.SelectedCMP116MarkedExpansion.domainAmplitude =
      domainAmplitude source
  ; R415.SelectedCMP116MarkedExpansion.domainAmplitudeNonnegative =
      domainAmplitudeNonnegative source
  ; R415.SelectedCMP116MarkedExpansion.commonYShellBelowDomainDecay =
      commonYShellBelowDomainDecay source
  ; R415.SelectedCMP116MarkedExpansion.sourceAmplitude =
      sourceAmplitude source
  ; R415.SelectedCMP116MarkedExpansion.amplitudeSumBelowSourceAmplitude =
      amplitudeSumBelowSourceAmplitude source
  }

literalCommonYWeightBelowShell :
  ∀ {Domain Term Operator}
    (source :
      LiteralTwoWilsonCMP116MarkedExpansionSource Domain Term Operator)
    domain →
  absℝ (commonYBoundaryIntegrand source domain)
  ≤ℝ commonYShell source domain
literalCommonYWeightBelowShell source =
  R415.commonYAbsoluteBoundFromR410 (asR415 source)

literalMarkedBoundaryBelowSourceDecay :
  ∀ {Domain Term Operator}
    (source :
      LiteralTwoWilsonCMP116MarkedExpansionSource Domain Term Operator) →
  absℝ (selectedBoundaryIntegrand source)
  ≤ℝ
  sourceAmplitude source
    *ℝ R414.weight (decay source)
      (R411.selectedConnectingDistance (geometry source))
literalMarkedBoundaryBelowSourceDecay source =
  R415.selectedBoundaryBelowSourceDecay (asR415 source)

literalTwoWilsonR413ToR415CompilerLevel : ProofLevel
literalTwoWilsonR413ToR415CompilerLevel = machineChecked

-- Remaining source-native theorem: construct the literal CMP116 terms/domains
-- and supply R413 path replays, scalarization, fixed-Y source summability and
-- two-mark support/rate data.  All noncommutative four-stage inequalities and
-- W1/W3 finite resummation are compiler output above.
