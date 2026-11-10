{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.KakeyaYMSelectedSpatialMetricWeldExact where

------------------------------------------------------------------------
-- REUSE-FIRST KAKeya / YANG--MILLS / LORENTZ (3,1) SAME-SOURCE SEAM
--
-- Original Kakeya theorem: Hong Wang, Joshua Zahl, arXiv:2502.17655;
-- streamlined proof: Larry Guth, Hong Wang, Joshua Zahl,
-- arXiv:2601.14411. Historical Lorentz, Minkowski, Kaluza/Klein,
-- Hodge, Wilson, and Osterwalder/Schrader work remains attributed
-- to its original authors.
--
-- Own contribution: explicit *conditional* transport of the SAME
-- PR #1460 observer-selected KK horizontal bilinear to a selected
-- Euclidean-spatial Gram form. No new signature derivation, no copied
-- KK proof, no physical instance, no Kakeya proof, no new axioms.
--
-- Spatial(v) is essential: an indefinite 3+1 bilinear cannot equal
-- a positive Euclidean Gram on all four-dimensional tangents.
-- The Euclidean identification is an original-source hypothesis,
-- not an assertion inferred from the sign count or same time arrow.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Foundations.TSFVFiltrationArrowLorentzBridgeExact as Arrow
import DASHI.Physics.Foundations.TSFVKKSameMetricTransportExact as Same
import DASHI.Physics.Foundations.TSFVKKSameArrowQuadraticMetricWeldExact as TimeAxis
import DASHI.Physics.Foundations.TSFVKKSelectedHorizontalMetricSchurExact as Horizontal
import DASHI.Physics.Foundations.TSFVKKActualSelectedMetricHorizontalWeldExact as Actual
import DASHI.Physics.Foundations.Lorentz31DirectionalProbeExact as L31
import DASHI.Physics.YangMills.YMClayLorentz31DirectionalKKHodgeExact as KK

module _
    (selected : Same.SameMetricTSFVKK)
    {Tangent SpatialCoordinates : Set}
    (isSpatial : Tangent → Set)
    (coordinates : Tangent → SpatialCoordinates)
    (euclideanSpatialGram : SpatialCoordinates → SpatialCoordinates → ℚ)
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
    (selectedObservedSpatialIsEuclidean :
      ∀ v w →
      isSpatial v → isSpatial w →
      observedBilinear
        (Arrow.SelectedTSFVToLorentzPhysicalSource.selectedState
          (Same.arrowSource selected)) v w
      ≡ euclideanSpatialGram (coordinates v) (coordinates w))
  where

  -- The first equality is inherited from the *actual selected* 5D
  -- horizontal/Schur theorem, rather than reconstructing it from
  -- the abstract signature profile.
  sameKKHorizontalSpatialGram :
    ∀ v w →
    isSpatial v → isSpatial w →
    fiveBilinear
      (KK.SameSourceKKYMContinuation.selectedMetric5D
        (Same.kkSource selected))
      v (Horizontal.horizontalCircleComponent connection v)
      w (Horizontal.horizontalCircleComponent connection w)
    ≡ euclideanSpatialGram (coordinates v) (coordinates w)
  sameKKHorizontalSpatialGram v w hv hw =
    trans
      (Actual.selectedKK5HorizontalIsActualObservedBilinear
        selected
        observedBilinear fourBilinear fiveBilinear
        connection radiusSquared
        selectedFiveMetricIsActualKKForm
        selectedObserverBilinearIsSameFourMetric v w)
      (selectedObservedSpatialIsEuclidean v w hv hw)

  -- One physical input still guarantees the original observed arrow
  -- is the arrow of the SAME source-selected KK metric.
  sameKKSpatialGramAndOriginalArrow :
    ∀ v w →
    isSpatial v → isSpatial w →
    (fiveBilinear
      (KK.SameSourceKKYMContinuation.selectedMetric5D
        (Same.kkSource selected))
      v (Horizontal.horizontalCircleComponent connection v)
      w (Horizontal.horizontalCircleComponent connection w)
      ≡ euclideanSpatialGram (coordinates v) (coordinates w))
    ×
    (L31.selectedArrow
       (KK.SameSourceKKYMContinuation.observedDirectionalEvidence
         (Same.kkSource selected))
     ≡
     L31.selectedArrow
       (Arrow.SelectedTSFVToLorentzPhysicalSource.uniqueMeasuredArrow
         (Same.arrowSource selected)))
  sameKKSpatialGramAndOriginalArrow v w hv hw =
    sameKKHorizontalSpatialGram v w hv hw ,
    TimeAxis.samePhysicalObserverAndKKTimeAxis selected

------------------------------------------------------------------------
-- REMAINING ORIGINAL-SOURCE LEAVES
-- Physical inhabitation of SameMetricTSFVKK and the two selected
-- metric equalities; actual spatial subbundle / positive metric and
-- coordinates; continuum completion and Euclidean isometry;
-- Lebesgue/Borel geometry and delta-tube direction transport;
-- the separately formalised 3D Kakeya theorem verification.
------------------------------------------------------------------------
