module DASHI.Physics.Foundations.TSFVConeArrowStringFibreOwnerBridgeExact where

-- Attribution, 2026-11-18:
-- * Classical: Sylvester inertia; Kaluza/Klein metric horizontal reduction;
--   Aharonov-Bergmann-Lebowitz / TSVF; standard fibre-bundle projections.
-- * Existing DASHI: Lorentz31DirectionalProbeExact,
--   TSFVFiltrationArrowLorentzBridgeExact,
--   TSFVKKSameMetricTransportExact,
--   TSFVKKFiveMetricInvertibleShearExact,
--   CalabiYau369CompactFibreBridge, U1SU2GroupTorusExact.
-- * User research: trace the original cone/arrow selection and connect
--   string/369 compact fibres without presuming a physical string.
-- * New: source-preserving conditional receipts for SAME TSFV state
--   and fibre projection; no new physical metric or SUSY claim.
--
-- Important: a proof for an arbitrary supplied physical-source RECORD
-- does not construct an inhabitant of that record.

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans; sym; cong)

import DASHI.Physics.Foundations.Lorentz31DirectionalProbeExact as Probe
import DASHI.Physics.Foundations.TSFVFiltrationArrowLorentzBridgeExact as TSFV
import DASHI.Physics.Foundations.TSFVKKSameMetricTransportExact as Metric
import DASHI.Geometry.CalabiYau369CompactFibreBridge as Fibre
import DASHI.Physics.YangMills.YMClayLorentz31DirectionalKKHodgeExact as KK

-- The existing TSFV proof does not assume a literal 31 mask,
-- but requires a selected measured-arrow probe and physical calibration.
-- We preserve their exact source instead of reconstructing an arrow.
sourceTSFVMeasuredQuadraticIs31 :
  (w : TSFV.SelectedTSFVToLorentzPhysicalSource) →
  Probe.actualAxisCounts
    (TSFV.SelectedTSFVToLorentzPhysicalSource.physicalQuadraticAxisSigns w
      (TSFV.SelectedTSFVToLorentzPhysicalSource.selectedState w))
    ≡ Probe.signature 3 1
sourceTSFVMeasuredQuadraticIs31 =
  TSFV.selectedTSFVPhysicalSignatureIs31

-- The SAME selected reduced KK metric is already transported from that
-- TSFV source: this is not a second, independently chosen 31 code.
sameMetricObserverSelectionIs31 :
  (w : Metric.SameMetricTSFVKK) →
  Probe.actualAxisCounts
    (KK.SameSourceKKYMContinuation.signatureSigns
      (Metric.SameMetricTSFVKK.kkSource w))
    ≡ Probe.signature 3 1
sameMetricObserverSelectionIs31 =
  Metric.sameMetricKKSignatureFromTSFV

-- A genuine fibre projection supplies an exact commuting base square.
-- This is an old lemma implied directly by the existing bundle axiom,
-- newly recorded as a consumer of the original 369 compact-fibre carrier.
fibreProjectionReturnsOriginalBase :
  ∀ {B I T : Set} →
  (f : Fibre.BaseCompactFibreBundle B I T) →
  (b : B) (i : I) →
  Fibre.BaseCompactFibreBundle.projectBase f
    (Fibre.BaseCompactFibreBundle.includeFibre f b i) ≡ b
fibreProjectionReturnsOriginalBase f =
  Fibre.BaseCompactFibreBundle.projectionReturnsBase f

-- If a worldsheet target is specifically a fine-bundle field
-- and its base observable is supplied, projection recovers that base.
-- This does not construct a worldsheet embedding, action, Weyl/BRST,
-- target spin structure, or selected SUSY vacuum.
worldsheetBaseProjectionCommutes :
  ∀ {Sigma B I T : Set} →
  (f : Fibre.BaseCompactFibreBundle B I T) →
  (baseMap : Sigma → B) →
  (internalMap : Sigma → I) →
  (s : Sigma) →
  Fibre.BaseCompactFibreBundle.projectBase f
    (Fibre.BaseCompactFibreBundle.includeFibre f
      (baseMap s) (internalMap s)) ≡ baseMap s
worldsheetBaseProjectionCommutes f baseMap internalMap s =
  Fibre.BaseCompactFibreBundle.projectionReturnsBase f
    (baseMap s) (internalMap s)
