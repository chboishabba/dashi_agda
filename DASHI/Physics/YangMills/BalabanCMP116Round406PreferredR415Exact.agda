{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116Round406PreferredR415Exact where

------------------------------------------------------------------------
-- B / ROUND406 -> PREFERRED R415 WITHOUT A SECOND CHARGING THEOREM
--
-- The Round406 literal selected CMP116 replay already owns
--
--   sum differentiatedTermMajorant <= commonYShell.
--
-- If the exact R410 replay identifies that majorant with R415's canonical
-- marked-product majorant, the newer Round354 charging interface can be
-- inhabited with the canonical majorant itself as the charged majorant.
--
-- Hence H_charge is reflexive on this route, and H_sum is transported from
-- the theorem-bearing Round406 positive sum.  The only genuinely new B data
-- left after the exact term replay are the selected two-mark geometry and
-- per-domain decay/amplitude accounting.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false)
open import Data.Rational.Base as ℚ using (ℚ)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; absℝ; _*ℝ_; _≤ℝ_; ≤ℝ-refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116SelectedTermwiseLocalizationRound406Exact as R406
import DASHI.Physics.YangMills.BalabanCMP116CanonicalPathMarkedReplayRound410Exact as R410
import DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedExpansionRound415Exact as R415
import DASHI.Physics.YangMills.BalabanCMP116Round354To415FixedYExact as FixedY
import DASHI.Physics.YangMills.BalabanCMP116Round406To415Exact as R406R415
import DASHI.Physics.YangMills.BalabanCMP116PreferredR415SourceExact as Preferred
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportConnectionRound411Exact as R411
import DASHI.Physics.YangMills.BalabanCMP116ConnectingOuterSumRound414Exact as R414
import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum

canonicalR410SumIsRound406MajorantSum :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (application : R406.SelectedCMP116TermwiseLocalization base)
    (replay : R406R415.Round406ExactR410Replay application)
    domain →
  Resum.sumℝ
    (λ term →
      R415.canonicalTermMajorant
        (R406R415.selectedR410Term replay domain term))
    (R406.termsWithCommonY application domain)
  ≡
  Resum.sumℝ
    (R406.differentiatedTermMajorant application domain)
    (R406.termsWithCommonY application domain)
canonicalR410SumIsRound406MajorantSum application replay domain =
  R406R415.sumCongruent
    (R406.termsWithCommonY application domain)
    (λ term →
      R415.canonicalTermMajorant
        (R406R415.selectedR410Term replay domain term))
    (R406.differentiatedTermMajorant application domain)
    (λ term →
      sym
        (R406R415.differentiatedMajorantIsCanonicalR410
          replay domain term))

round406FixedYCharging :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (application : R406.SelectedCMP116TermwiseLocalization base)
    (replay : R406R415.Round406ExactR410Replay application) →
  FixedY.R415FixedYCharging
    (R406.termsWithCommonY application)
    (R406R415.selectedR410Term replay)
    (R406.commonYShell application)
round406FixedYCharging application replay = record
  { FixedY.R415FixedYCharging.chargedMajorant =
      λ domain term →
        R415.canonicalTermMajorant
          (R406R415.selectedR410Term replay domain term)
  ; FixedY.R415FixedYCharging.canonicalR410BelowCharged =
      λ domain term → ≤ℝ-refl
  ; FixedY.R415FixedYCharging.chargedCMP116Summability =
      λ domain →
        subst
          (λ selectedSum →
            selectedSum ≤ℝ R406.commonYShell application domain)
          (sym
            (canonicalR410SumIsRound406MajorantSum
              application replay domain))
          (R406.differentiatedMajorantsBelowCommonYShell
            application domain)
  }

compilePreferredFromRound406 :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (application : R406.SelectedCMP116TermwiseLocalization base)
    (replay : R406R415.Round406ExactR410Replay application)
    (geometryData : R406R415.Round406To415Geometry application) →
  Preferred.PreferredR415Source
    (R406.Domain application)
    (R406.Term application)
    (R406.Operator application)
compilePreferredFromRound406 application replay geometryData = record
  { Preferred.PreferredR415Source.localizedDomains =
      R406.localizedDomains application
  ; Preferred.PreferredR415Source.termsWithCommonY =
      R406.termsWithCommonY application
  ; Preferred.PreferredR415Source.selectedTerm =
      R406R415.selectedR410Term replay
  ; Preferred.PreferredR415Source.commonYBoundaryIntegrand =
      R406.commonYBoundaryIntegrand application
  ; Preferred.PreferredR415Source.commonYShell =
      R406.commonYShell application
  ; Preferred.PreferredR415Source.selectedBoundaryIntegrand =
      R406.selectedBoundaryIntegrand application
  ; Preferred.PreferredR415Source.commonYBoundaryIsSelectedTermSum =
      λ domain →
        trans
          (R406.commonYBoundaryIsTermSum application domain)
          (R406R415.sumCongruent
            (R406.termsWithCommonY application domain)
            (R406.differentiatedTerm application domain)
            (λ term →
              R410.differentiatedTerm
                (R406R415.selectedR410Term replay domain term))
            (R406R415.differentiatedTermIsR410 replay domain))
  ; Preferred.PreferredR415Source.selectedBoundaryIsCommonYSum =
      R406.selectedBoundaryIsCommonYSum application
  ; Preferred.PreferredR415Source.fixedYCharging =
      round406FixedYCharging application replay
  ; Preferred.PreferredR415Source.geometry =
      R406R415.geometry geometryData
  ; Preferred.PreferredR415Source.decay =
      R406R415.decay geometryData
  ; Preferred.PreferredR415Source.everyLocalizedDomainConnects =
      R406R415.everyLocalizedDomainConnects geometryData
  ; Preferred.PreferredR415Source.domainAmplitude =
      R406R415.domainAmplitude geometryData
  ; Preferred.PreferredR415Source.domainAmplitudeNonnegative =
      R406R415.domainAmplitudeNonnegative geometryData
  ; Preferred.PreferredR415Source.commonYShellBelowDomainDecay =
      R406R415.commonYShellBelowDomainDecay geometryData
  ; Preferred.PreferredR415Source.sourceAmplitude =
      R406R415.sourceAmplitude geometryData
  ; Preferred.PreferredR415Source.amplitudeSumBelowSourceAmplitude =
      R406R415.amplitudeSumBelowSourceAmplitude geometryData
  }

round406PreferredSelectedBoundaryDecay :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (application : R406.SelectedCMP116TermwiseLocalization base)
    (replay : R406R415.Round406ExactR410Replay application)
    (geometryData : R406R415.Round406To415Geometry application) →
  absℝ
    (R406.selectedBoundaryIntegrand application)
  ≤ℝ
  R406R415.sourceAmplitude geometryData
    *ℝ
    R414.weight
      (R406R415.decay geometryData)
      (R411.selectedConnectingDistance
        (R406R415.geometry geometryData))
round406PreferredSelectedBoundaryDecay application replay geometryData =
  Preferred.preferredR415SelectedBoundaryDecay
    (compilePreferredFromRound406 application replay geometryData)

round406ToPreferredR415CompilerLevel : ProofLevel
round406ToPreferredR415CompilerLevel = machineChecked

-- On the R406 route there is no independent H_charge/H_sum research leaf:
-- exact R410 replay + existing R406 positive summability pays both.
round406SeparateMarkedChargingLeafRequired : Bool
round406SeparateMarkedChargingLeafRequired = false

round406SeparateMarkedChargingLeafRequiredIsFalse :
  round406SeparateMarkedChargingLeafRequired ≡ false
round406SeparateMarkedChargingLeafRequiredIsFalse = refl

-- Remaining physical inhabitants on this route:
--   B1 exact R406 term = R410 term/majorant,
--   B4-B7 selected two-mark geometry and domain amplitude/tree decay.
literalRound406R410ReplayAndConnectingGeometryLevel : ProofLevel
literalRound406R410ReplayAndConnectingGeometryLevel = conditional
