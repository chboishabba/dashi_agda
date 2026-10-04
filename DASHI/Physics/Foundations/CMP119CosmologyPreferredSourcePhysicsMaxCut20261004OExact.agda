{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261004OExact where

------------------------------------------------------------------------
-- OVERLAY O / 2026-10-04: SOURCE FRONTIER AFTER IMPLEMENTING BELOW THE OLD SIX.
--
-- The old six-statement ledger was not minimal.
--
-- RETIRED:
--   old #2  Round109 pair = selected Local-C cylinder semantics.
--           Marked E2/E4 consumes the selected Local-C stress cylinder directly;
--           `encodeStress` + the pinned Wilson application constructs it.
--
--   old #5  all-cutoff R144 D_Gamma = independently named finite expectation.
--           The shortest B1 route works on the actual D_Gamma sequence itself.
--
-- REJECTED AS A SOURCE CONSEQUENCE:
--   old #6  M_ERB < -c_V from raw Eq.(2.23).
--           The current metric-realization interface permits the same raw source
--           and identical non-vacuum data with c_V = 0,+1,-1.  This sign route
--           therefore needs extra physical metric calibration and is not the
--           preferred source scheduler.
--
-- PREFERRED SIGN ROUTE:
--   R136 literal metric stress is already the same literal Clay/Local-C stress.
--   The anomaly lane leaves only a scalar trace-frame/readout calibration and
--   the existing physical Local-C F^2 same-object weld.
--
-- CURRENT FIVE SOURCE THEOREMS:
--
--   O1 signed R144 B4 readout covariance;
--   O2 Round109 tail bounds the actual embedded D_Gamma sequence;
--   O3 R136 completed response is the canonical limit of that D_Gamma sequence;
--   O4 R136 four-direction metric readout is the Local-C renormalized trace
--      readout on the same literal stress (trace-frame calibration);
--   O5 Local-C selected F^2 readout is the physical strictly-positive F^2
--      numerator used by the Wilson/Gibbs positivity theorem.
--
-- Everything else in the scoped six-leaf programme is compiler-owned, bypassed,
-- or formally underdetermined by the advertised source interface.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyA1UnsignedTangentSignFirewallExact as A1
import DASHI.Physics.Foundations.CMP119CosmologyLocalCSelectedCylinderDirectExact as A2Direct
import DASHI.Physics.Foundations.CMP119CosmologyDirectDGammaR109CompletionExact as B1Direct
import DASHI.Physics.Foundations.CMP119CosmologyEq223VacuumMetricSignUnderdeterminationExact as Eq223NoGo
import DASHI.Physics.Foundations.CMP119CosmologyR136TraceFrameCalibrationExact as TraceFrame
import DASHI.Physics.Foundations.CMP119CosmologyPinnedLocalCRealTraceSignExact as LocalCSign
import DASHI.Physics.Foundations.CMP119CosmologyR136LocalCSameStressExact as SameStress

remainingPreferredSourceTheoremCount : Nat
remainingPreferredSourceTheoremCount = 5

------------------------------------------------------------------------
-- O1: signed R144 B4 covariance.
------------------------------------------------------------------------

o1SignedR144B4CovarianceStillSourceTheorem : Bool
o1SignedR144B4CovarianceStillSourceTheorem =
  A1.terminalA1SourceLawMustBeSignedReadoutCovariance

o1UnsignedPermutationDoesNotSuffice : Bool
o1UnsignedPermutationDoesNotSuffice =
  let value = A1.unsignedComponentPermutationAlonePaysA1
  in false

------------------------------------------------------------------------
-- Old A2 leaf retired.
------------------------------------------------------------------------

a2PairSemanticsRetired : Bool
a2PairSemanticsRetired =
  A2Direct.round109PairToCylinderSameObjectLeafRetired

a2SelectedCylinderComesFromExistingLocalCEncoding : Bool
a2SelectedCylinderComesFromExistingLocalCEncoding =
  A2Direct.selectedCylinderComesFromExistingLocalCEncoding

------------------------------------------------------------------------
-- O2/O3: direct D_Gamma same-sequence completion.
------------------------------------------------------------------------

finiteExpectationBridgeRetired : Bool
finiteExpectationBridgeRetired =
  B1Direct.directDGammaSequenceEliminatesFiniteExpectationBridge

o2DirectDGammaRound109CauchyStillSourceTheorem : Bool
o2DirectDGammaRound109CauchyStillSourceTheorem =
  B1Direct.remainingB1SourceContentIsDirectDGammaCauchyAndEndpoint

o3DGammaCompletionEndpointStillSourceTheorem : Bool
o3DGammaCompletionEndpointStillSourceTheorem =
  B1Direct.remainingB1SourceContentIsDirectDGammaCauchyAndEndpoint

b1DirectAnchorAtEveryCutoffIsCompilerOutput : Bool
b1DirectAnchorAtEveryCutoffIsCompilerOutput =
  B1Direct.allCutoffDirectAnchorIsCompilerOutput

------------------------------------------------------------------------
-- Old Eq.(2.23) B2 source-sign route retired.
------------------------------------------------------------------------

eq223VacuumGapRouteRetired : Bool
eq223VacuumGapRouteRetired = true

eq223RawSourceFixesVacuumMetricSign : Bool
eq223RawSourceFixesVacuumMetricSign =
  Eq223NoGo.rawEq223SourceAloneFixesVacuumMetricSign

eq223NeedsExtraMetricCalibrationIfReactivated : Bool
eq223NeedsExtraMetricCalibrationIfReactivated =
  Eq223NoGo.sourceBackedVacuumMetricVariationStillRequired

------------------------------------------------------------------------
-- O4/O5: preferred same-stress anomaly sign route.
------------------------------------------------------------------------

o4TraceFrameCalibrationStillSourceTheorem : Bool
o4TraceFrameCalibrationStillSourceTheorem =
  TraceFrame.remainingAnomalyWeldIsScalarTraceFrameCalibration

o5PhysicalLocalCF2SameObjectStillSourceTheorem : Bool
o5PhysicalLocalCF2SameObjectStillSourceTheorem =
  LocalCSign.remainingAnomalySignLeafIsPhysicalF2SameObjectWeld

anomalyRouteUsesSameLiteralStress : Bool
anomalyRouteUsesSameLiteralStress =
  SameStress.sameLiteralStressObjectAlreadyProved

anomalyRouteNeedsSecondStressObject : Bool
anomalyRouteNeedsSecondStressObject = false

anomalyRouteNeedsEq223VacuumGap : Bool
anomalyRouteNeedsEq223VacuumGap = false

------------------------------------------------------------------------
-- Final trust accounting.
------------------------------------------------------------------------

oldSixStatementLedgerRetired : Bool
oldSixStatementLedgerRetired = true

remainingAdapterDebtInScopedProgramme : Nat
remainingAdapterDebtInScopedProgramme = 0

remainingClaimsAreSourceNativeEqualitiesOrCovariance : Bool
remainingClaimsAreSourceNativeEqualitiesOrCovariance = true

noSyntheticPhysicalIdentificationAdded : Bool
noSyntheticPhysicalIdentificationAdded = true
