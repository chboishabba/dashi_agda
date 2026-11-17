module DASHI.Governance.BoloBoloComparatorWorkloadLowerBoundExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- COMPARATOR-LOCAL GOVERNANCE WORKLOAD LOWER BOUNDS.
--
-- These coordinates are deliberately local to the institutions and source
-- versions that report them.  They are not transported into a bolo target.
--
-- Historical Porto Alegre PB source coordinates:
--   * 44-member Participatory Budgeting Council;
--   * council convenes for meetings of at least 120 minutes each week during
--     the cited July-September budget phase.
-- DASHI arithmetic therefore yields a conservative council-layer floor of
--   44 * 120 = 5280 council-person-minutes/week = 88 person-hours/week.
-- This excludes preparation, travel, delegate forums, reporting, informal
-- discussion and all other participation work.
--
-- Mondragon sources pay cadence rather than duration:
--   * Management Council reports to Governing Council at least monthly;
--   * Social Council / Faculty Board representatives meet represented members
--     monthly and the representative body handles major issues monthly.
-- These establish recurring accountability/reportback work but no duration or
-- target cost coefficient.
------------------------------------------------------------------------

record ComparatorWorkloadLowerBound : Set where
  constructor comparatorWorkloadLowerBound
  field
    portoHistoricalCouncilMembers : Nat
    portoHistoricalMinimumMeetingMinutesPerWeek : Nat
    portoHistoricalMinimumCouncilPersonMinutesPerWeek : Nat
    portoHistoricalMinimumCouncilPersonHoursPerWeek : Nat
    mondragonManagementToGoverningAtLeastMonthly : Bool
    mondragonRepresentativeToRepresentedMonthly : Bool
    mondragonRepresentativeBodyMajorIssuesMonthly : Bool

open ComparatorWorkloadLowerBound public

canonicalComparatorWorkloadLowerBound : ComparatorWorkloadLowerBound
canonicalComparatorWorkloadLowerBound =
  comparatorWorkloadLowerBound
    44 120 5280 88
    true true true

portoHistoricalCouncilPersonMinutesArithmetic : 44 * 120 ≡ 5280
portoHistoricalCouncilPersonMinutesArithmetic = refl

portoHistoricalCouncilPersonHoursArithmetic : 88 * 60 ≡ 5280
portoHistoricalCouncilPersonHoursArithmetic = refl

record ComparatorWorkloadBoundary : Set where
  constructor comparatorWorkloadBoundary
  field
    councilLayerHasPositiveObservedTimeWorkload : Bool
    councilPersonMinutesAreTotalParticipatoryWorkload : Bool
    omittedPreparationTravelAndReportingAssumedZero : Bool
    mondragonMonthlyCadenceIdentifiesMeetingDuration : Bool
    comparatorWorkloadIsTargetBoloBoundaryCost : Bool
    comparatorWorkloadIsPerUnitCausalCostWeight : Bool
    comparatorWorkloadCanRefuteZeroOverheadToyModels : Bool
    explicitTransportStillRequired : Bool

open ComparatorWorkloadBoundary public

canonicalComparatorWorkloadBoundary : ComparatorWorkloadBoundary
canonicalComparatorWorkloadBoundary =
  comparatorWorkloadBoundary
    true false false false false false true true

canonicalComparatorWorkloadLowerBoundReceipt : GenericReceipt.GenericReceipt
canonicalComparatorWorkloadLowerBoundReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo comparator-local governance workload lower bound"
    "DASHI.Governance.BoloBoloComparatorWorkloadLowerBoundExact"
    "canonicalComparatorWorkloadLowerBound / canonicalComparatorWorkloadBoundary"
    "derives a conservative historical Porto Alegre council-layer floor of 5280 council-person-minutes, or 88 council-person-hours, per week from the source-paid 44-member council and at-least-120-minute weekly meeting cadence, while separately recording monthly Mondragon accountability/reportback cadence"
    "the Porto Alegre floor covers only the cited council meeting layer and excludes preparation, travel, delegate forums, reporting and informal work; Mondragon cadence supplies no duration; neither comparator-local workload is a target bolo cost bound or causal per-unit weight and any transfer remains separately justified"
    "agda -i . DASHI/Governance/BoloBoloComparatorWorkloadLowerBoundRegression.agda"
