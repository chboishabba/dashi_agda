module DASHI.Governance.BoloBoloComparatorWorkloadLowerBoundRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloComparatorWorkloadLowerBoundExact as Workload

portoCouncilMembersPinned :
  Workload.portoHistoricalCouncilMembers Workload.canonicalComparatorWorkloadLowerBound ≡ 44
portoCouncilMembersPinned = refl

portoMinutesPinned :
  Workload.portoHistoricalMinimumCouncilPersonMinutesPerWeek Workload.canonicalComparatorWorkloadLowerBound ≡ 5280
portoMinutesPinned = refl

portoHoursPinned :
  Workload.portoHistoricalMinimumCouncilPersonHoursPerWeek Workload.canonicalComparatorWorkloadLowerBound ≡ 88
portoHoursPinned = refl

mondragonMonthlyReportingPinned :
  Workload.mondragonManagementToGoverningAtLeastMonthly Workload.canonicalComparatorWorkloadLowerBound ≡ true
mondragonMonthlyReportingPinned = refl

notTargetBoloCost :
  Workload.comparatorWorkloadIsTargetBoloBoundaryCost Workload.canonicalComparatorWorkloadBoundary ≡ false
notTargetBoloCost = refl

transportStillRequired :
  Workload.explicitTransportStillRequired Workload.canonicalComparatorWorkloadBoundary ≡ true
transportStillRequired = refl
