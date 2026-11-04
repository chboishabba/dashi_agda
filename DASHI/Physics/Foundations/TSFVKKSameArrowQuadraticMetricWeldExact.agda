{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSFVKKSameArrowQuadraticMetricWeldExact where

------------------------------------------------------------------------
-- P02/P07: SAME OBSERVED ARROW, not just SAME (3,1) signature count.
--
-- The existing SameMetricTSFVKK has (i) original observer-filtration
-- selected quadratic signs, (ii) source-selected KK-reduced metric signs,
-- (iii) pointwise sign agreement at the same physical metric state.
-- BOTH owners already calibrate their probe to those selected signs.
--
-- Because classifyProbe : Bool -> AxisSign is injective, the selected
-- KK directional probe must agree AT EVERY AXIS with the actual original
-- observer-derived probe. No second arrow-choice physical premise, no
-- arbitrary function extensionality, no 31-coded constructor.
--
-- This is stronger than merely comparing signature counts. The physical
-- inhabitation of SameMetricTSFVKK and the physical observer/OS Hamiltonian
-- identity remain genuinely OPEN. This source is an implication theorem,
-- not a constructed physical (3,1), KK metric or Stone evolution.
--
-- Original authorships: Aharonov--Bergmann--Lebowitz, Aharonov--Vaidman,
-- Lorentz/Sylvester/Minkowski, Kaluza/Klein, Osterwalder--Schrader;
-- corresponding DASHI original theorem owners remain imported.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)
open import Data.Empty using (⊥; ⊥-elim)

import DASHI.Physics.Foundations.Lorentz31DirectionalProbeExact as L31
import DASHI.Physics.Foundations.TSFVFiltrationArrowLorentzBridgeExact as Arrow
import DASHI.Physics.Foundations.TSFVKKSameMetricTransportExact as Same
import DASHI.Physics.YangMills.YMClayLorentz31DirectionalKKHodgeExact as KK

-- This is TRUE for the original two constructors and is not a generic
-- assertion that an arbitrary direction classifier can be inverted.
classifyProbeInjective :
  ∀ (left right : Bool) →
  L31.classifyProbe left ≡ L31.classifyProbe right →
  left ≡ right
classifyProbeInjective true true equality = refl
classifyProbeInjective true false ()
classifyProbeInjective false true ()
classifyProbeInjective false false equality = refl

-- The key stronger same-object equation. At every original axis,
-- recover the KK observed cone probe from the selected observer's
-- independently declared measurement, via the SAME reduced metric's
-- quadratic signs. This is not inferred from matching 3+1 count alone.
sameMetricKKObservedProbeEqualsTSFV :
  (w : Same.SameMetricTSFVKK) →
  (axis : L31.Axis) →
  KK.SameSourceKKYMContinuation.signatureProbe (Same.kkSource w) axis
  ≡
  Arrow.SelectedTSFVToLorentzPhysicalSource.measuredPrincipalAxisProbe
    (Same.arrowSource w)
    (Arrow.SelectedTSFVToLorentzPhysicalSource.selectedState
      (Same.arrowSource w))
    axis
sameMetricKKObservedProbeEqualsTSFV w axis =
  classifyProbeInjective
    (KK.SameSourceKKYMContinuation.signatureProbe (Same.kkSource w) axis)
    (Arrow.SelectedTSFVToLorentzPhysicalSource.measuredPrincipalAxisProbe
      (Same.arrowSource w)
      (Arrow.SelectedTSFVToLorentzPhysicalSource.selectedState
        (Same.arrowSource w)) axis)
    (trans
      (sym
        (L31.AxisCalibration.matchesActualQuadratic
          (KK.SameSourceKKYMContinuation.sameMetricCalibration
            (Same.kkSource w)) axis))
      (trans
        (Same.selectedMetricSignsAreArrowQuadraticSigns w axis)
        (trans
          (cong
            (λ state →
              Arrow.SelectedTSFVToLorentzPhysicalSource.physicalQuadraticAxisSigns
                (Same.arrowSource w) state axis)
            (Same.selectedStateIsReducedMetric w))
          (L31.AxisCalibration.matchesActualQuadratic
            (Arrow.SelectedTSFVToLorentzPhysicalSource.calibratedQuadratic
              (Same.arrowSource w)) axis))))

-- A genuinely constructed KK-side directional witness, not the
-- already-stored independent KK proof. Its four booleans originate in
-- the ORIGINAL TSFV measured physical state.
sameMetricKKDirectionFromTSFV :
  (w : Same.SameMetricTSFVKK) →
  L31.DirectionalProbe
    (KK.SameSourceKKYMContinuation.signatureProbe (Same.kkSource w))
sameMetricKKDirectionFromTSFV w with
  Arrow.SelectedTSFVToLorentzPhysicalSource.uniqueMeasuredArrow
    (Same.arrowSource w)
... | L31.arrow0 h0 h1 h2 h3 =
  L31.arrow0
    (trans (sameMetricKKObservedProbeEqualsTSFV w L31.axis0) h0)
    (trans (sameMetricKKObservedProbeEqualsTSFV w L31.axis1) h1)
    (trans (sameMetricKKObservedProbeEqualsTSFV w L31.axis2) h2)
    (trans (sameMetricKKObservedProbeEqualsTSFV w L31.axis3) h3)
... | L31.arrow1 h0 h1 h2 h3 =
  L31.arrow1
    (trans (sameMetricKKObservedProbeEqualsTSFV w L31.axis0) h0)
    (trans (sameMetricKKObservedProbeEqualsTSFV w L31.axis1) h1)
    (trans (sameMetricKKObservedProbeEqualsTSFV w L31.axis2) h2)
    (trans (sameMetricKKObservedProbeEqualsTSFV w L31.axis3) h3)
... | L31.arrow2 h0 h1 h2 h3 =
  L31.arrow2
    (trans (sameMetricKKObservedProbeEqualsTSFV w L31.axis0) h0)
    (trans (sameMetricKKObservedProbeEqualsTSFV w L31.axis1) h1)
    (trans (sameMetricKKObservedProbeEqualsTSFV w L31.axis2) h2)
    (trans (sameMetricKKObservedProbeEqualsTSFV w L31.axis3) h3)
... | L31.arrow3 h0 h1 h2 h3 =
  L31.arrow3
    (trans (sameMetricKKObservedProbeEqualsTSFV w L31.axis0) h0)
    (trans (sameMetricKKObservedProbeEqualsTSFV w L31.axis1) h1)
    (trans (sameMetricKKObservedProbeEqualsTSFV w L31.axis2) h2)
    (trans (sameMetricKKObservedProbeEqualsTSFV w L31.axis3) h3)

-- Any two exact directional certificates on ONE Boolean measured
-- probe select the SAME axis; their source-specific proof data need
-- not be propositionally identical.
trueCannotEqualFalse : true ≡ false → ⊥
trueCannotEqualFalse ()

selectedArrowUnique :
  ∀ {p : L31.Axis → Bool} →
  (first second : L31.DirectionalProbe p) →
  L31.selectedArrow first ≡ L31.selectedArrow second
selectedArrowUnique
  (L31.arrow0 _ _ _ _) (L31.arrow0 _ _ _ _) = refl
selectedArrowUnique
  (L31.arrow0 t0 _ _ _) (L31.arrow1 f0 _ _ _) =
    ⊥-elim (trueCannotEqualFalse (trans (sym t0) f0))
selectedArrowUnique
  (L31.arrow0 t0 _ _ _) (L31.arrow2 f0 _ _ _) =
    ⊥-elim (trueCannotEqualFalse (trans (sym t0) f0))
selectedArrowUnique
  (L31.arrow0 t0 _ _ _) (L31.arrow3 f0 _ _ _) =
    ⊥-elim (trueCannotEqualFalse (trans (sym t0) f0))
selectedArrowUnique
  (L31.arrow1 f0 _ _ _) (L31.arrow0 t0 _ _ _) =
    ⊥-elim (trueCannotEqualFalse (trans (sym t0) f0))
selectedArrowUnique
  (L31.arrow1 _ t1 _ _) (L31.arrow1 _ _ _ _) = refl
selectedArrowUnique
  (L31.arrow1 _ t1 _ _) (L31.arrow2 _ f1 _ _) =
    ⊥-elim (trueCannotEqualFalse (trans (sym t1) f1))
selectedArrowUnique
  (L31.arrow1 _ t1 _ _) (L31.arrow3 _ f1 _ _) =
    ⊥-elim (trueCannotEqualFalse (trans (sym t1) f1))
selectedArrowUnique
  (L31.arrow2 f0 _ _ _) (L31.arrow0 t0 _ _ _) =
    ⊥-elim (trueCannotEqualFalse (trans (sym t0) f0))
selectedArrowUnique
  (L31.arrow2 _ f1 _ _) (L31.arrow1 _ t1 _ _) =
    ⊥-elim (trueCannotEqualFalse (trans (sym t1) f1))
selectedArrowUnique
  (L31.arrow2 _ _ t2 _) (L31.arrow2 _ _ _ _) = refl
selectedArrowUnique
  (L31.arrow2 _ _ t2 _) (L31.arrow3 _ _ f2 _) =
    ⊥-elim (trueCannotEqualFalse (trans (sym t2) f2))
selectedArrowUnique
  (L31.arrow3 f0 _ _ _) (L31.arrow0 t0 _ _ _) =
    ⊥-elim (trueCannotEqualFalse (trans (sym t0) f0))
selectedArrowUnique
  (L31.arrow3 _ f1 _ _) (L31.arrow1 _ t1 _ _) =
    ⊥-elim (trueCannotEqualFalse (trans (sym t1) f1))
selectedArrowUnique
  (L31.arrow3 _ _ f2 _) (L31.arrow2 _ _ t2 _) =
    ⊥-elim (trueCannotEqualFalse (trans (sym t2) f2))
selectedArrowUnique
  (L31.arrow3 _ _ _ t3) (L31.arrow3 _ _ _ _) = refl

-- The constructed KK certificate selects exactly the original TSFV axis.
derivedKKSelectedAxisIsOriginal :
  (w : Same.SameMetricTSFVKK) →
  L31.selectedArrow (sameMetricKKDirectionFromTSFV w)
  ≡ L31.selectedArrow
      (Arrow.SelectedTSFVToLorentzPhysicalSource.uniqueMeasuredArrow
        (Same.arrowSource w))
derivedKKSelectedAxisIsOriginal w with
  Arrow.SelectedTSFVToLorentzPhysicalSource.uniqueMeasuredArrow
    (Same.arrowSource w)
... | L31.arrow0 _ _ _ _ = refl
... | L31.arrow1 _ _ _ _ = refl
... | L31.arrow2 _ _ _ _ = refl
... | L31.arrow3 _ _ _ _ = refl

-- MAIN P02/P07 same-object arrow theorem: even the original KK source's
-- *preexisting* certificate and the original TSVF observer certificate
-- must select one and the same physical axis, not just identical counts.
samePhysicalObserverAndKKTimeAxis :
  (w : Same.SameMetricTSFVKK) →
  L31.selectedArrow
    (KK.SameSourceKKYMContinuation.observedDirectionalEvidence
      (Same.kkSource w))
  ≡
  L31.selectedArrow
    (Arrow.SelectedTSFVToLorentzPhysicalSource.uniqueMeasuredArrow
      (Same.arrowSource w))
samePhysicalObserverAndKKTimeAxis w =
  trans
    (selectedArrowUnique
      (KK.SameSourceKKYMContinuation.observedDirectionalEvidence
        (Same.kkSource w))
      (sameMetricKKDirectionFromTSFV w))
    (derivedKKSelectedAxisIsOriginal w)

-- NOTE: SameMetricTSFVKK is still UNINHABITED by physical dynamics.
-- Axis equality cannot establish equality of physical metrics, real
-- generator domains, Wick continuation, or a Clay mass gap.
