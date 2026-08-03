module DASHI.Physics.Closure.NSTriadKNAnalyticBlockerAuthorityAudit where

------------------------------------------------------------------------
-- PURPOSE
-- Distinguish three levels for the two Stage-3 blockers:
--
--   1. exact finite/cutoff-indexed mathematics;
--   2. identification with the repository's legacy or physical NS objects;
--   3. promotion authority.
--
-- Blocker 1 now has a postulate-free cutoff-indexed depth carrier and exact
-- FT->adv / FT->trans weight orientation.  The old globally bounded
-- Nat-indexed depth API is not used by this replacement because it cannot
-- support arbitrary cutoff-dependent separation.  The remaining seam is the
-- classifier/index identification from the legacy Stage-3 entries to the new
-- cutoff-indexed carrier.
--
-- Blocker 2 now has an inhabited exact unit-shell operator/error/base-gap
-- ladder and a strict positive margin.  The remaining seam is the equality of
-- the canonical finite weighted-Schur operator with the physical PDE
-- pair-incidence operator.
--
-- No BKM or Clay promotion gate is changed here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNProfileCrossWeightBridge as WeightBridge
import DASHI.Physics.Closure.NSTriadKNProfileDepthGeometryCutoffIndexedExact
  as CutoffDepth
import DASHI.Physics.Closure.NSTriadKNResidueScaleOperatorGapExact
  as ResidueGap

------------------------------------------------------------------------
-- Strong authority receipt carrying proof terms from both exact lanes.
------------------------------------------------------------------------

record ExactAnalyticBlockerAuthority : Set₁ where
  constructor authority
  field
    cutoffIndexedDepthGeometry :
      CutoffDepth.CutoffIndexedProfileDepthGeometry

    ftAdvOrientation :
      (N : _) →
      (incidence : CutoffDepth.FTToAdversarialIncidence N) →
      Agda.Builtin.Nat.suc N
        Agda.Builtin.Nat.*
        CutoffDepth.weightOf N (CutoffDepth.ftAdvTarget incidence)
        Data.Nat.≤
      CutoffDepth.weightOf N (CutoffDepth.ftAdvSource incidence)

    ftTransOrientation :
      (N : _) →
      (incidence : CutoffDepth.FTToTransitionIncidence N) →
      Agda.Builtin.Nat.suc N
        Agda.Builtin.Nat.*
        CutoffDepth.weightOf N (CutoffDepth.ftTransTarget incidence)
        Data.Nat.≤
      CutoffDepth.weightOf N (CutoffDepth.ftTransSource incidence)

    residueScaleOperatorGap :
      ResidueGap.ExactResidueScaleOperatorGapAuthority

open ExactAnalyticBlockerAuthority public

exactAnalyticBlockerAuthority : ExactAnalyticBlockerAuthority
exactAnalyticBlockerAuthority =
  authority
    CutoffDepth.canonicalCutoffIndexedProfileDepthGeometry
    CutoffDepth.ftAdvWeightOrientation
    CutoffDepth.ftTransWeightOrientation
    ResidueGap.exactResidueScaleOperatorGapAuthority

------------------------------------------------------------------------
-- Honest closed/open ledger.
------------------------------------------------------------------------

blocker1LegacyRestrictedRowRouteAssembled : Bool
blocker1LegacyRestrictedRowRouteAssembled =
  WeightBridge.blocker1DepthRouteClosed

blocker1LegacyRestrictedRowRouteAssembledIsTrue :
  blocker1LegacyRestrictedRowRouteAssembled ≡ true
blocker1LegacyRestrictedRowRouteAssembledIsTrue =
  WeightBridge.blocker1DepthRouteClosedIsTrue

blocker1CutoffIndexedDepthGeometryConstructed : Bool
blocker1CutoffIndexedDepthGeometryConstructed =
  CutoffDepth.cutoffIndexedProfileDepthGeometryConstructed

blocker1CutoffIndexedDepthGeometryConstructedIsTrue :
  blocker1CutoffIndexedDepthGeometryConstructed ≡ true
blocker1CutoffIndexedDepthGeometryConstructedIsTrue =
  CutoffDepth.cutoffIndexedProfileDepthGeometryConstructedIsTrue

blocker1BothWeightOrientationsConstructed : Bool
blocker1BothWeightOrientationsConstructed = true

blocker1BothWeightOrientationsConstructedIsTrue :
  blocker1BothWeightOrientationsConstructed ≡ true
blocker1BothWeightOrientationsConstructedIsTrue = refl

blocker1LegacyNatEntryIdentificationClosed : Bool
blocker1LegacyNatEntryIdentificationClosed =
  CutoffDepth.legacyNatEntryIdentificationClosed

blocker1LegacyNatEntryIdentificationClosedIsFalse :
  blocker1LegacyNatEntryIdentificationClosed ≡ false
blocker1LegacyNatEntryIdentificationClosedIsFalse =
  CutoffDepth.legacyNatEntryIdentificationClosedIsFalse

blocker1PhysicalAuthorityClosed : Bool
blocker1PhysicalAuthorityClosed = false

blocker1PhysicalAuthorityClosedIsFalse :
  blocker1PhysicalAuthorityClosed ≡ false
blocker1PhysicalAuthorityClosedIsFalse = refl

blocker2FiniteCanonicalOperatorGapAuthorityConstructed : Bool
blocker2FiniteCanonicalOperatorGapAuthorityConstructed =
  ResidueGap.finiteCanonicalOperatorGapAuthorityConstructed

blocker2FiniteCanonicalOperatorGapAuthorityConstructedIsTrue :
  blocker2FiniteCanonicalOperatorGapAuthorityConstructed ≡ true
blocker2FiniteCanonicalOperatorGapAuthorityConstructedIsTrue =
  ResidueGap.finiteCanonicalOperatorGapAuthorityConstructedIsTrue

blocker2ResidueScaleCompatibilityConstructed : Bool
blocker2ResidueScaleCompatibilityConstructed =
  ResidueGap.residueScaleCompatibilityConstructed

blocker2ResidueScaleCompatibilityConstructedIsTrue :
  blocker2ResidueScaleCompatibilityConstructed ≡ true
blocker2ResidueScaleCompatibilityConstructedIsTrue =
  ResidueGap.residueScaleCompatibilityConstructedIsTrue

blocker2PhysicalPairIncidenceKernelIdentificationClosed : Bool
blocker2PhysicalPairIncidenceKernelIdentificationClosed =
  ResidueGap.physicalPairIncidenceKernelIdentificationClosed

blocker2PhysicalPairIncidenceKernelIdentificationClosedIsFalse :
  blocker2PhysicalPairIncidenceKernelIdentificationClosed ≡ false
blocker2PhysicalPairIncidenceKernelIdentificationClosedIsFalse =
  ResidueGap.physicalPairIncidenceKernelIdentificationClosedIsFalse

blocker2PhysicalAuthorityClosed : Bool
blocker2PhysicalAuthorityClosed = false

blocker2PhysicalAuthorityClosedIsFalse :
  blocker2PhysicalAuthorityClosed ≡ false
blocker2PhysicalAuthorityClosedIsFalse = refl

bothFiniteAnalyticCoresConstructed : Bool
bothFiniteAnalyticCoresConstructed = true

bothFiniteAnalyticCoresConstructedIsTrue :
  bothFiniteAnalyticCoresConstructed ≡ true
bothFiniteAnalyticCoresConstructedIsTrue = refl

bothPhysicalAnalyticBlockersClosed : Bool
bothPhysicalAnalyticBlockersClosed = false

bothPhysicalAnalyticBlockersClosedIsFalse :
  bothPhysicalAnalyticBlockersClosed ≡ false
bothPhysicalAnalyticBlockersClosedIsFalse = refl

analyticBlockerAuthorityBoundaryAudited : Bool
analyticBlockerAuthorityBoundaryAudited = true

analyticBlockerAuthorityBoundaryAuditedIsTrue :
  analyticBlockerAuthorityBoundaryAudited ≡ true
analyticBlockerAuthorityBoundaryAuditedIsTrue = refl
