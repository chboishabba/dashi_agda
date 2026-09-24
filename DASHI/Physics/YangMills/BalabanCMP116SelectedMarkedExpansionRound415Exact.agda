{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedExpansionRound415Exact where

------------------------------------------------------------------------
-- ROUND415 / SELECTED R410 TERMS -> CMP116 CONNECTING SOURCE DECAY
--
-- Preferred literal B composition:
--
--   exact selected R410 four-stage scalar terms
--       -> R404 common-Y absolute sum
--       -> R414 connecting-domain positive sum
--       -> selected source decay.
--
-- This avoids rebuilding an independent R406 operator-factor carrier at the
-- terminal composition point.  Every term below is already a
-- SelectedCMP116PathMarkedTerm, so its noncommutative bound is R410 output.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; absℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum
import DASHI.Physics.YangMills.BalabanNoncommutativeMarkedOperatorProductExact as Marked
import DASHI.Physics.YangMills.BalabanCMP109FourStageOperatorFactorRound407Exact as R407
import DASHI.Physics.YangMills.BalabanCMP99MarkedStageDifferenceRound408Exact as R408
import DASHI.Physics.YangMills.BalabanCMP99SingleMarkedFourStageRound409Exact as R409
import DASHI.Physics.YangMills.BalabanCMP116CanonicalPathMarkedReplayRound410Exact as R410
import DASHI.Physics.YangMills.BalabanCMP116AbsoluteWalkResummationRound404Exact as R404
import DASHI.Physics.YangMills.BalabanCMP116NestedSourceSummationRound405Exact as R405
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportConnectionRound411Exact as R411
import DASHI.Physics.YangMills.BalabanCMP116ConnectingOuterSumRound414Exact as R414

canonicalTermMajorant :
  ∀ {Operator} →
  R410.SelectedCMP116PathMarkedTerm Operator → ℝ
canonicalTermMajorant term =
  Marked.markedProductMajorant
    (R408.telescopeAlgebra
      (R410.stageDifference (R410.replay term)))
    (R407.ordinaryStageMajorant
      (R408.ordinaryPair
        (R410.stageDifference (R410.replay term))))
    (R409.stageMarkedMajorant
      (R410.stageDifference (R410.replay term))
      (R410.canonicalSingleChangedAgreement (R410.replay term)))
    R407.cmp109DerivativeStages

record SelectedCMP116MarkedExpansion
    (Domain Term Operator : Set) : Set₁ where
  field
    localizedDomains : List Domain
    termsWithCommonY : Domain → List Term

    selectedTerm :
      Domain → Term → R410.SelectedCMP116PathMarkedTerm Operator

    commonYBoundaryIntegrand commonYShell : Domain → ℝ
    selectedBoundaryIntegrand : ℝ

    -- Literal source expansion equalities.
    commonYBoundaryIsSelectedTermSum :
      ∀ domain →
      commonYBoundaryIntegrand domain
      ≡
      Resum.sumℝ
        (λ term →
          R410.differentiatedTerm (selectedTerm domain term))
        (termsWithCommonY domain)

    selectedBoundaryIsCommonYSum :
      selectedBoundaryIntegrand
      ≡ Resum.sumℝ commonYBoundaryIntegrand localizedDomains

    -- CMP116 fixed-Y walk/tree counting after the R410 factor estimate.
    selectedR410MajorantsBelowCommonYShell :
      ∀ domain →
      Resum.sumℝ
        (λ term → canonicalTermMajorant (selectedTerm domain term))
        (termsWithCommonY domain)
      ≤ℝ commonYShell domain

    -- Selected support geometry + outer localization counting.
    geometry : R411.SelectedSupportConnectionGeometry Domain Term
    decay : R414.AntitoneNonnegativeDecayWeight

    everyLocalizedDomainConnects :
      ∀ domain → R411.domainConnectsBothSupports geometry domain

    domainAmplitude : Domain → ℝ
    domainAmplitudeNonnegative :
      ∀ domain → 0ℝ ≤ℝ domainAmplitude domain

    commonYShellBelowDomainDecay :
      ∀ domain →
      commonYShell domain
      ≤ℝ domainAmplitude domain
        *ℝ R414.weight decay (R411.domainTreeDistance geometry domain)

    sourceAmplitude : ℝ

    amplitudeSumBelowSourceAmplitude :
      Resum.sumℝ domainAmplitude localizedDomains
      ≤ℝ sourceAmplitude

open SelectedCMP116MarkedExpansion public

selectedTermBelowCanonicalMajorant :
  ∀ {Domain Term Operator}
    (expansion : SelectedCMP116MarkedExpansion Domain Term Operator)
    domain term →
  absℝ
    (R410.differentiatedTerm
      (selectedTerm expansion domain term))
  ≤ℝ
  canonicalTermMajorant
    (selectedTerm expansion domain term)
selectedTermBelowCanonicalMajorant expansion domain term =
  R410.selectedDifferentiatedTermBelowCanonicalMarkedProduct
    (selectedTerm expansion domain term)

commonYAbsoluteBoundFromR410 :
  ∀ {Domain Term Operator}
    (expansion : SelectedCMP116MarkedExpansion Domain Term Operator)
    domain →
  absℝ (commonYBoundaryIntegrand expansion domain)
  ≤ℝ commonYShell expansion domain
commonYAbsoluteBoundFromR410 expansion domain =
  R404.cmp116CommonYAbsoluteBoundaryBound
    (termsWithCommonY expansion domain)
    (λ term →
      R410.differentiatedTerm
        (selectedTerm expansion domain term))
    (λ term →
      canonicalTermMajorant
        (selectedTerm expansion domain term))
    (commonYBoundaryIntegrand expansion domain)
    (commonYShell expansion domain)
    (commonYBoundaryIsSelectedTermSum expansion domain)
    (selectedTermBelowCanonicalMajorant expansion domain)
    (selectedR410MajorantsBelowCommonYShell expansion domain)

asConnectingOuterSumData :
  ∀ {Domain Term Operator}
    (expansion : SelectedCMP116MarkedExpansion Domain Term Operator) →
  R414.ConnectingOuterSumData
    Domain Term (geometry expansion) (decay expansion)
asConnectingOuterSumData expansion = record
  { R414.ConnectingOuterSumData.localizedDomains =
      localizedDomains expansion
  ; R414.ConnectingOuterSumData.everyLocalizedDomainConnects =
      everyLocalizedDomainConnects expansion
  ; R414.ConnectingOuterSumData.domainAmplitude =
      domainAmplitude expansion
  ; R414.ConnectingOuterSumData.domainAmplitudeNonnegative =
      domainAmplitudeNonnegative expansion
  ; R414.ConnectingOuterSumData.commonYShell =
      commonYShell expansion
  ; R414.ConnectingOuterSumData.commonYShellBelowDomainDecay =
      commonYShellBelowDomainDecay expansion
  ; R414.ConnectingOuterSumData.sourceAmplitude =
      sourceAmplitude expansion
  ; R414.ConnectingOuterSumData.amplitudeSumBelowSourceAmplitude =
      amplitudeSumBelowSourceAmplitude expansion
  }

outerShellSumBelowSelectedDecay :
  ∀ {Domain Term Operator}
    (expansion : SelectedCMP116MarkedExpansion Domain Term Operator) →
  Resum.sumℝ (commonYShell expansion) (localizedDomains expansion)
  ≤ℝ
  sourceAmplitude expansion
        *ℝ R414.weight (decay expansion)
        (R411.selectedConnectingDistance (geometry expansion))
outerShellSumBelowSelectedDecay expansion =
  R414.connectingOuterSumBelowSelectedDecay
    (asConnectingOuterSumData expansion)

selectedBoundaryBelowSourceDecay :
  ∀ {Domain Term Operator}
    (expansion : SelectedCMP116MarkedExpansion Domain Term Operator) →
  absℝ (selectedBoundaryIntegrand expansion)
  ≤ℝ
  sourceAmplitude expansion
        *ℝ R414.weight (decay expansion)
        (R411.selectedConnectingDistance (geometry expansion))
selectedBoundaryBelowSourceDecay expansion =
  R405.cmp116NestedAbsoluteBoundaryLocalization
    (localizedDomains expansion)
    (commonYBoundaryIntegrand expansion)
    (commonYShell expansion)
    (selectedBoundaryIntegrand expansion)
    (sourceAmplitude expansion
        *ℝ R414.weight (decay expansion)
          (R411.selectedConnectingDistance (geometry expansion)))
    (selectedBoundaryIsCommonYSum expansion)
    (commonYAbsoluteBoundFromR410 expansion)
    (outerShellSumBelowSelectedDecay expansion)

round415R410ToCommonYCompilerLevel : ProofLevel
round415R410ToCommonYCompilerLevel = machineChecked

round415ConnectingOuterSumCompilerLevel : ProofLevel
round415ConnectingOuterSumCompilerLevel = machineChecked

round415SelectedSourceDecayCompilerLevel : ProofLevel
round415SelectedSourceDecayCompilerLevel = machineChecked

-- Remaining B source content on this preferred owner:
-- * enumerate the literal CMP116 differentiated terms as exact R410 terms;
-- * prove the fixed-Y R410-majorant sum;
-- * prove every surviving selected Y connects both marks;
-- * produce per-Y amplitudes with a uniform finite amplitude sum.
literalCMP116SelectedR410ExpansionAndCountingLevel : ProofLevel
literalCMP116SelectedR410ExpansionAndCountingLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
