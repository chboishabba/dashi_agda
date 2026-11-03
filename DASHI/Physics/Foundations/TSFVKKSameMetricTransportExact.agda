{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSFVKKSameMetricTransportExact where

-- Same-metric seam: original finite history/observer-filtration arrow
-- is selected by the SAME reduced four-dimensional metric consumed by
-- the Yang--Mills/KK continuation. This module does not supply that
-- physical identification from finite histories alone.
--
-- Reuse/attribution:
-- * DASHI FiniteHistoryOrientationExact / HistoryWeightFiltrationExact:
--   original finite reversal, filtering and future-boundary results.
-- * DASHI TSFVFiltrationArrowLorentzBridgeExact: source-indexed operational
--   temporal arrow and conditional physical principal-axis certificate.
-- * DASHI YMClayLorentz31DirectionalKKHodgeExact: the selected KK reduction
--   and Euclidean-YM Osterwalder--Schrader physical continuation contract.
-- * Lorentz/Sylvester and Osterwalder--Schrader historical mathematics
--   remains credited to the original authors, not this adapter.
--
-- No postulates, holes, TERMINATING pragmas or claims of Clay completion.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans; sym)

import DASHI.Physics.Foundations.Lorentz31DirectionalProbeExact as L31
import DASHI.Physics.Foundations.TSFVFiltrationArrowLorentzBridgeExact as Arrow
import DASHI.Physics.YangMills.YMClayLorentz31DirectionalKKHodgeExact as KK

-- A selected KK four-metric must represent the VERY SAME physical
-- state whose two-boundary filtration supplies the observed arrow.
-- Pointwise sign correspondence must be established from that metric;
-- equality of two labels or two independently chosen "31" tags is not
-- accepted as a substitute.
record SameMetricTSFVKK : Set₁ where
  field
    arrowSource : Arrow.SelectedTSFVToLorentzPhysicalSource
    kkSource : KK.SameSourceKKYMContinuation

    physicalStateOfMetric :
      KK.SameSourceKKYMContinuation.Metric4D kkSource →
      Arrow.SelectedTSFVToLorentzPhysicalSource.PhysicalState arrowSource

    selectedStateIsReducedMetric :
      physicalStateOfMetric
        (KK.SameSourceKKYMContinuation.selectedMetric4D kkSource)
      ≡
      Arrow.SelectedTSFVToLorentzPhysicalSource.selectedState arrowSource

    selectedMetricSignsAreArrowQuadraticSigns :
      (a : L31.Axis) →
      KK.SameSourceKKYMContinuation.signatureSigns kkSource a
      ≡
      Arrow.SelectedTSFVToLorentzPhysicalSource.physicalQuadraticAxisSigns
        arrowSource
        (physicalStateOfMetric
          (KK.SameSourceKKYMContinuation.selectedMetric4D kkSource))
        a

open SameMetricTSFVKK public

-- A genuine commuting-sign proof. The KK/YM output is recovered from
-- the original TSFV-selected physical quadratic rather than from a
-- second arbitrary orientation count. No function extensionality axiom
-- is needed: all four selected axes are compared pointwise.
sameMetricKKSignatureFromTSFV :
  (w : SameMetricTSFVKK) →
  L31.actualAxisCounts
    (KK.SameSourceKKYMContinuation.signatureSigns (kkSource w))
  ≡ L31.signature 3 1
sameMetricKKSignatureFromTSFV w
  rewrite selectedMetricSignsAreArrowQuadraticSigns w L31.axis0
        | selectedMetricSignsAreArrowQuadraticSigns w L31.axis1
        | selectedMetricSignsAreArrowQuadraticSigns w L31.axis2
        | selectedMetricSignsAreArrowQuadraticSigns w L31.axis3
        | selectedStateIsReducedMetric w =
  Arrow.selectedTSFVPhysicalSignatureIs31 (arrowSource w)

-- The chosen time orientation is not merely a sign convention in this
-- finite calibrated basis: the reversed count contradicts the
-- source-selected operational/metric correspondence.
sameMetricKKReversedCountExcluded :
  (w : SameMetricTSFVKK) →
  L31.actualAxisCounts
    (KK.SameSourceKKYMContinuation.signatureSigns (kkSource w))
  ≡ L31.signature 1 3 →
  L31.⊥
sameMetricKKReversedCountExcluded w reversed =
  L31.threePlusOneDiffersFromOnePlusThree
    (trans (sym (sameMetricKKSignatureFromTSFV w)) reversed)

-- Importing this module does not construct SameMetricTSFVKK. Actual
-- observation -> metric-state correspondence and physical quadratic
-- comparison are still required. Nor does it construct R443 Haar,
-- R445 continuum, R320 decay, R333 spectral gap, KK source equality,
-- or the 4D OS reconstruction itself.
