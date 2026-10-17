module DASHI.Governance.BoloBoloComparatorInstitutionalVersioningExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- COMPARATOR INSTITUTIONS ARE TIME-INDEXED, NOT STATIC TYPES.
--
-- Historical Porto Alegre PB descriptions used elsewhere in this branch pin a
-- 16-region / ~1000-delegate / 44-member council architecture with weekly
-- council meetings during the cited budget phase.
--
-- The current City of Porto Alegre description in 2026 instead reports:
--   * 17 regional + 6 thematic assemblies = 23 assembly streams;
--   * regional/thematic delegate forums meeting every 15 days;
--   * a 92-councillor collegiate body also meeting every 15 days.
--
-- These are distinct institutional versions. DASHI must never combine the
-- historical 44-member count with current 2026 cadence/assembly coordinates as
-- though they were simultaneous properties of one fixed institution.
------------------------------------------------------------------------

record PortoAlegreHistoricalVersion : Set where
  constructor portoAlegreHistoricalVersion
  field
    historicalRegionCount : Nat
    historicalApproxDelegateCount : Nat
    historicalCouncilMemberCount : Nat
    historicalCouncilWeeklyMeeting : Bool

open PortoAlegreHistoricalVersion public

canonicalPortoAlegreHistoricalVersion : PortoAlegreHistoricalVersion
canonicalPortoAlegreHistoricalVersion =
  portoAlegreHistoricalVersion 16 1000 44 true

record PortoAlegreCurrent2026Version : Set where
  constructor portoAlegreCurrent2026Version
  field
    currentRegionCount : Nat
    currentThematicCount : Nat
    currentAssemblyStreamCount : Nat
    currentCouncillorCount : Nat
    delegateForumsEvery15Days : Bool
    councillorCollegiateEvery15Days : Bool

open PortoAlegreCurrent2026Version public

canonicalPortoAlegreCurrent2026Version : PortoAlegreCurrent2026Version
canonicalPortoAlegreCurrent2026Version =
  portoAlegreCurrent2026Version
    17 6 23 92 true true

currentAssemblyArithmetic : 17 + 6 ≡ 23
currentAssemblyArithmetic = refl

record ComparatorVersioningBoundary : Set where
  constructor comparatorVersioningBoundary
  field
    comparatorArchitectureMayEvolveOverTime : Bool
    historicalAndCurrentCoordinatesMayBeSplicedWithoutVersionWitness : Bool
    historical44AndCurrent92AreSameCouncilCount : Bool
    transportMustNameInstitutionalVersion : Bool
    longitudinalChangeCanInformAdaptationHypotheses : Bool
    institutionalChangeItselfProvesImprovement : Bool

open ComparatorVersioningBoundary public

canonicalComparatorVersioningBoundary : ComparatorVersioningBoundary
canonicalComparatorVersioningBoundary =
  comparatorVersioningBoundary
    true false false true true false

canonicalComparatorInstitutionalVersioningReceipt : GenericReceipt.GenericReceipt
canonicalComparatorInstitutionalVersioningReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo comparator institutional versioning"
    "DASHI.Governance.BoloBoloComparatorInstitutionalVersioningExact"
    "canonicalPortoAlegreHistoricalVersion / canonicalPortoAlegreCurrent2026Version / canonicalComparatorVersioningBoundary"
    "separates historical Porto Alegre participatory-budgeting coordinates from the current 2026 municipal architecture, which reports seventeen regional plus six thematic assembly streams and a ninety-two-councillor collegiate body with delegate and councillor meetings every fifteen days"
    "historical and current counts/cadences cannot be spliced into one synthetic comparator; any transport must identify the institutional version and institutional evolution by itself establishes neither efficiency improvement nor bolo optimality"
    "agda -i . DASHI/Governance/BoloBoloComparatorInstitutionalVersioningRegression.agda"
