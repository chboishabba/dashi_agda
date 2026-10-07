module DASHI.Physics.Closure.NSClayFacingCDPublicationAuditLedger20261007Exact where

------------------------------------------------------------------------
-- CLAY-FACING C/D / PUBLICATION AND REPRODUCIBILITY AUDIT LEDGER / 2026-10-07
--
-- Attribution-preserving audit owner; not a new Navier--Stokes proof.
--
-- In addition to the already-closed official statement-coordinate audit, the
-- current released Lean dependency routes were inspected at
-- f9e8bc5b38b6e212696e8a30e3e91517af887bbd:
--
-- C:
--   R3.ComparatorBridge.globalSolutionOfComparator preserves nu, force, zero
--   datum, equation, divergence and bounded-energy class; comparator_of_breakdown
--   feeds that same competitor into the theorem_1_1 global exclusion.
--
-- D:
--   PeriodicComparatorSolution.periodicPaperSolution_of_comparator preserves
--   nu, force, time, zero datum, equation and BOTH velocity/pressure periodicity;
--   PeriodicViscosity.excludes_global_solution uses finite-slab classical
--   uniqueness with the same positive viscosity/force/datum and contradicts
--   the candidate's unbounded speed at time one.
--
-- Thus these are now SOURCE-DEPENDENCY AUDITS.  They remain distinct from an
-- independently witnessed kernel build, independent reconstruction, referee
-- reproduction, or CMI adjudication.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSClayFacingCDSourceAuditExact as SourceAudit
import DASHI.Physics.Closure.NSOpenAI2026ComparatorClayCDSourceExactAlignment as Source
import DASHI.Physics.Closure.NSOpenAI2026ReleasedCDCurrentHeadAudit20261007Exact as Fresh

------------------------------------------------------------------------
-- Shared provenance / reproducibility receipts.
------------------------------------------------------------------------

currentReleasedHeadPinnedForAudit : Bool
currentReleasedHeadPinnedForAudit = true

currentHeadStatementFreshnessClosed : Bool
currentHeadStatementFreshnessClosed =
  Fresh.cComparatorStatementStableAcrossReleaseCommits

currentMetadataNoSorryAuditClosed : Bool
currentMetadataNoSorryAuditClosed = true

independentKernelBuildWitnessedHere : Bool
independentKernelBuildWitnessedHere = false

conventionalIndependentReconstructionClosed : Bool
conventionalIndependentReconstructionClosed = false

independentRefereeReproductionClosed : Bool
independentRefereeReproductionClosed = false

------------------------------------------------------------------------
-- C: statement-coordinate + released dependency-route audit.
------------------------------------------------------------------------

cStatementCoordinateAuditClosed : Bool
cStatementCoordinateAuditClosed = SourceAudit.cOfficialCoordinatesSourceAudited

cPositiveViscosityAudited : Bool
cPositiveViscosityAudited =
  Source.positiveViscosityC Source.releasedClayCSourceReceipt

cSmoothDivergenceFreeDatumAudited : Bool
cSmoothDivergenceFreeDatumAudited =
  Source.smoothDivergenceFreeDatumC Source.releasedClayCSourceReceipt

cRapidDatumDecayAudited : Bool
cRapidDatumDecayAudited =
  Source.rapidInitialSpatialDecayC Source.releasedClayCSourceReceipt

cSmoothForcingAudited : Bool
cSmoothForcingAudited =
  Source.smoothForcingC Source.releasedClayCSourceReceipt

cRapidForceSpaceTimeDecayAudited : Bool
cRapidForceSpaceTimeDecayAudited =
  Source.rapidForcingSpaceTimeDecayC Source.releasedClayCSourceReceipt

cExactEquationAudited : Bool
cExactEquationAudited =
  Source.exactEquationC Source.releasedClayCSourceReceipt

cBoundedEnergyConsumerAudited : Bool
cBoundedEnergyConsumerAudited =
  Source.boundedEnergyConsumerC Source.releasedClayCSourceReceipt

cNoGlobalSmoothSolutionAudited : Bool
cNoGlobalSmoothSolutionAudited =
  Source.noGlobalSmoothSolutionC Source.releasedClayCSourceReceipt

-- Current R3 bridge explicitly preserves the selected nu, prescribed force and
-- zero datum when a comparator solution is converted into a
-- GlobalFiniteEnergySolution.
cSameNuSameDataSameForceDependencyAuditClosed : Bool
cSameNuSameDataSameForceDependencyAuditClosed = true

-- globalSolutionOfComparator reconstructs the exact equation/divergence and
-- the comparator's uniformly bounded kinetic-energy condition on the paper's
-- GlobalFiniteEnergySolution structure.
cBoundedEnergyClassBridgeAuditClosed : Bool
cBoundedEnergyClassBridgeAuditClosed = true

-- theorem_1_1 produces CandidateProperties together with
-- ¬ Nonempty (GlobalFiniteEnergySolution nu f) for that same force.
cGlobalExclusionDependencyAuditClosed : Bool
cGlobalExclusionDependencyAuditClosed = true

cReleasedDependencyRouteSourceAudited : Bool
cReleasedDependencyRouteSourceAudited = true

------------------------------------------------------------------------
-- D: statement-coordinate + released dependency-route audit.
------------------------------------------------------------------------

dStatementCoordinateAuditClosed : Bool
dStatementCoordinateAuditClosed = SourceAudit.dOfficialCoordinatesSourceAudited

dAllPositiveViscositiesAudited : Bool
dAllPositiveViscositiesAudited =
  Source.positiveViscosityD Source.releasedClayDSourceReceipt

dSmoothDivergenceFreeDatumAudited : Bool
dSmoothDivergenceFreeDatumAudited =
  Source.smoothDivergenceFreeDatumD Source.releasedClayDSourceReceipt

dPeriodicDatumAudited : Bool
dPeriodicDatumAudited =
  Source.periodicInitialDatumD Source.releasedClayDSourceReceipt

dSmoothForcingAudited : Bool
dSmoothForcingAudited =
  Source.smoothForcingD Source.releasedClayDSourceReceipt

dPeriodicForcingAudited : Bool
dPeriodicForcingAudited =
  Source.periodicForcingD Source.releasedClayDSourceReceipt

dRapidForceTimeDecayAudited : Bool
dRapidForceTimeDecayAudited =
  Source.rapidForcingTimeDecayD Source.releasedClayDSourceReceipt

dExactEquationAudited : Bool
dExactEquationAudited =
  Source.exactEquationD Source.releasedClayDSourceReceipt

dPeriodicSolutionConsumerAudited : Bool
dPeriodicSolutionConsumerAudited =
  Source.periodicSolutionConsumerD Source.releasedClayDSourceReceipt

dNoGlobalSmoothSolutionAudited : Bool
dNoGlobalSmoothSolutionAudited =
  Source.noGlobalSmoothSolutionD Source.releasedClayDSourceReceipt

-- PeriodicPaperComparator and PeriodicComparatorSolution explicitly preserve
-- the selected positive viscosity, same force, zero datum and time variable.
dSameDataSameForceSameViscosityDependencyAuditClosed : Bool
dSameDataSameForceSameViscosityDependencyAuditClosed = true

-- PeriodicViscosity.excludes_global_solution calls
-- PeriodicViscosityUniqueness.classical_uniqueness_on_Icc on each t<1 slab.
dFiniteSlabUniquenessDependencyAuditClosed : Bool
dFiniteSlabUniquenessDependencyAuditClosed = true

-- CandidateProperties carries SpeedUnboundedAtOne and excludes a continuous
-- global extension by the finite-slab identification above.
dFiniteTimeUnboundednessDependencyAuditClosed : Bool
dFiniteTimeUnboundednessDependencyAuditClosed = true

-- A hypothetical comparator global solution is converted to a global smooth
-- periodic paper solution before applying the exclusion theorem.
dHypotheticalGlobalCompetitorBridgeAuditClosed : Bool
dHypotheticalGlobalCompetitorBridgeAuditClosed = true

-- periodicPaperSolution_of_comparator copies the comparator pressure periodicity
-- field explicitly, not merely velocity periodicity.
dPeriodicPressureDependencyAuditClosed : Bool
dPeriodicPressureDependencyAuditClosed = true

dReleasedDependencyRouteSourceAudited : Bool
dReleasedDependencyRouteSourceAudited = true

------------------------------------------------------------------------
-- Publication/adjudication boundary.
------------------------------------------------------------------------

cDStatementAuditIsInternalTheoremDiscovery : Bool
cDStatementAuditIsInternalTheoremDiscovery = false

clayPrizeAdjudicationClaimed : Bool
clayPrizeAdjudicationClaimed = false

------------------------------------------------------------------------
-- Regression receipts.
------------------------------------------------------------------------

cStatementCoordinateAuditClosedIsTrue : cStatementCoordinateAuditClosed ≡ true
cStatementCoordinateAuditClosedIsTrue = refl

dStatementCoordinateAuditClosedIsTrue : dStatementCoordinateAuditClosed ≡ true
dStatementCoordinateAuditClosedIsTrue = refl

cReleasedDependencyRouteSourceAuditedIsTrue :
  cReleasedDependencyRouteSourceAudited ≡ true
cReleasedDependencyRouteSourceAuditedIsTrue = refl

dReleasedDependencyRouteSourceAuditedIsTrue :
  dReleasedDependencyRouteSourceAudited ≡ true
dReleasedDependencyRouteSourceAuditedIsTrue = refl

currentReleasedHeadPinnedForAuditIsTrue : currentReleasedHeadPinnedForAudit ≡ true
currentReleasedHeadPinnedForAuditIsTrue = refl

currentMetadataNoSorryAuditClosedIsTrue : currentMetadataNoSorryAuditClosed ≡ true
currentMetadataNoSorryAuditClosedIsTrue = refl

independentKernelBuildWitnessedHereIsFalse : independentKernelBuildWitnessedHere ≡ false
independentKernelBuildWitnessedHereIsFalse = refl

conventionalIndependentReconstructionClosedIsFalse :
  conventionalIndependentReconstructionClosed ≡ false
conventionalIndependentReconstructionClosedIsFalse = refl

independentRefereeReproductionClosedIsFalse : independentRefereeReproductionClosed ≡ false
independentRefereeReproductionClosedIsFalse = refl

cDStatementAuditIsInternalTheoremDiscoveryIsFalse :
  cDStatementAuditIsInternalTheoremDiscovery ≡ false
cDStatementAuditIsInternalTheoremDiscoveryIsFalse = refl

clayPrizeAdjudicationClaimedIsFalse : clayPrizeAdjudicationClaimed ≡ false
clayPrizeAdjudicationClaimedIsFalse = refl
