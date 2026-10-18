{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261004PExact where

------------------------------------------------------------------------
-- OVERLAY P / 2026-10-04: FINAL PREFERRED SOURCE MAX-CUT FOR THIS TRANCHE.
--
-- The original six-statement schedule was overconstrained.  After implementing
-- below those interfaces, the preferred route is now the direct same-stress
-- Local-C anomaly route.  It never consumes finite D_Gamma sign transport.
--
-- RETIRED FROM THE PREFERRED ROUTE:
--
--   * Round109 pair -> selected Local-C cylinder semantics:
--       marked E2/E4 constructs the selected cylinder directly from the pinned
--       Local-C stress encoding + published Wilson application.
--
--   * finite-expectation / D_Gamma presentation bridge:
--       not needed by the direct anomaly route.
--
--   * Round109 finite-tail / completion sign lane:
--       remains a valid alternate construction, but is dominated for the
--       preferred sign proof because the continuum anomaly lane reaches R136
--       directly.
--
--   * raw Eq.(2.23) vacuum sign / M_ERB < -c_V:
--       not source-derivable from the current metric-realization interface;
--       the explicit no-go owner permits c_V = 0,+1,-1 on the same raw source
--       with all non-vacuum metric derivatives fixed.
--
-- THE THREE PREFERRED SOURCE THEOREMS ARE NOW EXACTLY:
--
-- P1. signed R144 B4 source/readout covariance;
--
-- P2. trace-frame calibration:
--       embedded R136 four-direction metric pairing
--         = renormalized Local-C stress-trace readout
--     on the already-proved SAME literal Clay/Local-C stress;
--
-- P3. physical F^2 same-object weld:
--       selected Local-C F^2 readout
--         = physical strictly-positive Wilson/Gibbs F^2 numerator.
--
-- Given P2+P3, the existing Local-C anomaly authority, SU(2) coefficient sign,
-- rational/real order reflection, and marked-OS terminal compilers produce the
-- negative R136 trace and positive matter acceleration contribution.
--
-- No adapter/source-presentation debt remains in this scoped preferred route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyA1UnsignedTangentSignFirewallExact as A1
import DASHI.Physics.Foundations.CMP119CosmologyLocalCSelectedCylinderDirectExact as A2Direct
import DASHI.Physics.Foundations.CMP119CosmologyR136TraceFrameCalibrationExact as TraceFrame
import DASHI.Physics.Foundations.CMP119CosmologyPinnedLocalCRealTraceSignExact as LocalCSign

remainingPreferredSourceTheoremCount : Nat
remainingPreferredSourceTheoremCount = 3

------------------------------------------------------------------------
-- P1: signed finite R144 B4 covariance.
------------------------------------------------------------------------

p1SignedR144B4CovarianceStillSourceTheorem : Bool
p1SignedR144B4CovarianceStillSourceTheorem =
  A1.terminalA1SourceLawMustBeSignedReadoutCovariance

p1UnsignedPermutationAloneSufficient : Bool
p1UnsignedPermutationAloneSufficient = false

------------------------------------------------------------------------
-- P2: same-stress trace-frame calibration.
------------------------------------------------------------------------

p2TraceFrameCalibrationStillSourceTheorem : Bool
p2TraceFrameCalibrationStillSourceTheorem =
  TraceFrame.remainingAnomalyWeldIsScalarTraceFrameCalibration

p2RequiresSecondStressObject : Bool
p2RequiresSecondStressObject = false

------------------------------------------------------------------------
-- P3: Local-C F^2 physical same-object weld.
------------------------------------------------------------------------

p3PhysicalLocalCF2SameObjectStillSourceTheorem : Bool
p3PhysicalLocalCF2SameObjectStillSourceTheorem =
  LocalCSign.remainingAnomalySignLeafIsPhysicalF2SameObjectWeld

------------------------------------------------------------------------
-- Retired / dominated lanes.
------------------------------------------------------------------------

a2PairSemanticsRetired : Bool
a2PairSemanticsRetired =
  A2Direct.round109PairToCylinderSameObjectLeafRetired

finiteTailRouteRetired : Bool
finiteTailRouteRetired = true

finiteDGammaSignTransportNeededByPreferredRoute : Bool
finiteDGammaSignTransportNeededByPreferredRoute = false

round109TailNeededByPreferredRoute : Bool
round109TailNeededByPreferredRoute = false

eq223RouteRetired : Bool
eq223RouteRetired = true

eq223VacuumMetricGapNeededByPreferredRoute : Bool
eq223VacuumMetricGapNeededByPreferredRoute = false

------------------------------------------------------------------------
-- Preferred route identity.
------------------------------------------------------------------------

preferredSignRouteIsDirectLocalCAnomaly : Bool
preferredSignRouteIsDirectLocalCAnomaly = true

preferredRouteUsesSameLiteralStressObject : Bool
preferredRouteUsesSameLiteralStressObject = true

preferredRouteNeedsSeparateSelectedQuantumTraceCarrier : Bool
preferredRouteNeedsSeparateSelectedQuantumTraceCarrier = false

remainingAdapterDebtInScopedPreferredRoute : Nat
remainingAdapterDebtInScopedPreferredRoute = 0

remainingPreferredClaimsAreSourceNativeCovarianceOrSameObjectCalibrations : Bool
remainingPreferredClaimsAreSourceNativeCovarianceOrSameObjectCalibrations = true

noSyntheticPhysicalIdentificationAdded : Bool
noSyntheticPhysicalIdentificationAdded = true
