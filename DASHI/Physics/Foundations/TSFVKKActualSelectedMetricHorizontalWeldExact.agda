{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSFVKKActualSelectedMetricHorizontalWeldExact where

------------------------------------------------------------------------
-- P02 -> P08: SAME SELECTED 5D METRIC / OBSERVER QUADRATIC, NO FIXTURE.
--
-- Consume the ORIGINAL SameMetricTSFVKK, which already shares one
-- physical observer state, one selected 5D metric, its selected reduced
-- 4D metric and the measured principal-axis calibration. Compose it
-- with the exact source-written KK5Bilinear horizontal/Schur identity.
--
-- The *only new physical proof inputs* are exactly the two nontrivial
-- metric equalities missing from the earlier source:
-- (a) the ACTUAL selected 5D metric's bilinear is the KK block form,
-- (b) the ACTUAL observer-measured 4D bilinear is the 4D metric
--     selected by that very same original KK reduction.
-- No equality is manufactured from a shared (3,1) signature count.
--
-- This gives an honest source-selected same-bilinear theorem:
--
--   G5_selected(h_A v,h_A w) = g_observed(selectedState)(v,w)
--                            = g4(reduce(G5_selected))(v,w).
--
-- and simultaneously retains the earlier proven identical observed
-- temporal axis. The other worker's standalone Clay YM is independent.
--
-- SOURCE conditional bridge, NOT construction of physical 5D Einstein
-- solutions, metric smoothness, real causal propagation or OS Hilbert.
-- Reuses exact original metric/observer and KK/Schur theorem owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Foundations.TSFVFiltrationArrowLorentzBridgeExact as Arrow
import DASHI.Physics.Foundations.TSFVKKSameMetricTransportExact as Same
import DASHI.Physics.Foundations.TSFVKKSameArrowQuadraticMetricWeldExact as TimeAxis
import DASHI.Physics.Foundations.TSFVKKSelectedHorizontalMetricSchurExact as Horizontal
import DASHI.Physics.Foundations.Lorentz31DirectionalProbeExact as L31
import DASHI.Physics.YangMills.YMClayLorentz31DirectionalKKHodgeExact as KK

module _
    (selected : Same.SameMetricTSFVKK)
    {Tangent : Set}
    (observedBilinear :
      Arrow.SelectedTSFVToLorentzPhysicalSource.PhysicalState
        (Same.arrowSource selected) →
      Tangent → Tangent → ℚ)
    (fourBilinear :
      KK.SameSourceKKYMContinuation.Metric4D
        (Same.kkSource selected) →
      Tangent → Tangent → ℚ)
    (fiveBilinear :
      KK.SameSourceKKYMContinuation.Metric5D
        (Same.kkSource selected) →
      Tangent → ℚ → Tangent → ℚ → ℚ)
    (connection : Tangent → ℚ)
    (radiusSquared : ℚ)
    (selectedFiveMetricIsActualKKForm :
      ∀ v fibreV w fibreW →
      fiveBilinear
        (KK.SameSourceKKYMContinuation.selectedMetric5D
          (Same.kkSource selected))
        v fibreV w fibreW
      ≡
      Horizontal.KK5Bilinear
        (fourBilinear
          (KK.SameSourceKKYMContinuation.selectedMetric4D
            (Same.kkSource selected)))
        connection radiusSquared
        v fibreV w fibreW)
    (selectedObserverBilinearIsSameFourMetric :
      ∀ v w →
      observedBilinear
        (Arrow.SelectedTSFVToLorentzPhysicalSource.selectedState
          (Same.arrowSource selected)) v w
      ≡
      fourBilinear
        (KK.SameSourceKKYMContinuation.selectedMetric4D
          (Same.kkSource selected)) v w)
  where

  selectedKK5HorizontalIsActualObservedBilinear :
    ∀ v w →
    fiveBilinear
      (KK.SameSourceKKYMContinuation.selectedMetric5D
        (Same.kkSource selected))
      v (Horizontal.horizontalCircleComponent connection v)
      w (Horizontal.horizontalCircleComponent connection w)
    ≡
    observedBilinear
      (Arrow.SelectedTSFVToLorentzPhysicalSource.selectedState
        (Same.arrowSource selected)) v w
  selectedKK5HorizontalIsActualObservedBilinear v w =
    trans
      (selectedFiveMetricIsActualKKForm
        v (Horizontal.horizontalCircleComponent connection v)
        w (Horizontal.horizontalCircleComponent connection w))
      (trans
        (Horizontal.actualKKHorizontalReductionIsOriginalFourMetric
          (fourBilinear
            (KK.SameSourceKKYMContinuation.selectedMetric4D
              (Same.kkSource selected)))
          connection radiusSquared v w)
        (sym (selectedObserverBilinearIsSameFourMetric v w)))

  -- The VERY SAME selected 5D metric, not some second 5D metric, is
  -- reduced by the existing original KK owner.
  selectedKKHorizontalEqualsReductionOfActualFiveMetric :
    ∀ v w →
    fiveBilinear
      (KK.SameSourceKKYMContinuation.selectedMetric5D
        (Same.kkSource selected))
      v (Horizontal.horizontalCircleComponent connection v)
      w (Horizontal.horizontalCircleComponent connection w)
    ≡
    fourBilinear
      (KK.SameSourceKKYMContinuation.reduceKKMetric
        (Same.kkSource selected)
        (KK.SameSourceKKYMContinuation.selectedMetric5D
          (Same.kkSource selected))) v w
  selectedKKHorizontalEqualsReductionOfActualFiveMetric v w =
    trans
      (selectedFiveMetricIsActualKKForm
        v (Horizontal.horizontalCircleComponent connection v)
        w (Horizontal.horizontalCircleComponent connection w))
      (trans
        (Horizontal.actualKKHorizontalReductionIsOriginalFourMetric
          (fourBilinear
            (KK.SameSourceKKYMContinuation.selectedMetric4D
              (Same.kkSource selected)))
          connection radiusSquared v w)
        (cong (λ metric → fourBilinear metric v w)
          (sym
            (KK.SameSourceKKYMContinuation.selectedMetricIsKKReduction
              (Same.kkSource selected)))))

  -- Combined result: exact numerical horizontal bilinear + EXACT
  -- identical KK and original observer-selected timelike direction.
  -- Both still depend on a physically inhabited selected input.
  selectedSameBilinearAndSameObserverArrow :
    ∀ v w →
    (fiveBilinear
      (KK.SameSourceKKYMContinuation.selectedMetric5D
        (Same.kkSource selected))
      v (Horizontal.horizontalCircleComponent connection v)
      w (Horizontal.horizontalCircleComponent connection w)
      ≡
      observedBilinear
        (Arrow.SelectedTSFVToLorentzPhysicalSource.selectedState
          (Same.arrowSource selected)) v w)
    ×
    (L31.selectedArrow
      (KK.SameSourceKKYMContinuation.observedDirectionalEvidence
        (Same.kkSource selected))
      ≡
      L31.selectedArrow
        (Arrow.SelectedTSFVToLorentzPhysicalSource.uniqueMeasuredArrow
          (Same.arrowSource selected)))
  selectedSameBilinearAndSameObserverArrow v w =
    selectedKK5HorizontalIsActualObservedBilinear v w ,
    TimeAxis.samePhysicalObserverAndKKTimeAxis selected

-- FAIL-CLOSED: Neither a 5D metric bilinear source nor the equivalence
-- of its selected 4D reduction with the observer-measured quadratic is
-- generated here. The two assumptions above are the exact P02/P08
-- physical producer leaves, rather than arbitrary metric witness labels.
