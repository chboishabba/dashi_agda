module DASHI.Governance.BoloBoloMondragonCorporationGovernanceCapacityRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloMondragonCorporationGovernanceCapacityExact as M

annualCongressRepresentativesPinned :
  M.annualCongressRepresentativeCount M.canonicalMondragonCorporationGovernanceCapacity ≡ 650
annualCongressRepresentativesPinned = refl

governingBodyMembersPinned :
  M.governingBodyMemberCount2021 M.canonicalMondragonCorporationGovernanceCapacity ≡ 665
governingBodyMembersPinned = refl

trainingHoursPinned :
  M.cooperativeTrainingHours2021 M.canonicalMondragonCorporationGovernanceCapacity ≡ 11703
trainingHoursPinned = refl

monthlyGovernanceMeetingsPaid :
  M.governingBodiesMeetMonthly M.canonicalMondragonCorporationGovernanceCapacity ≡ true
monthlyGovernanceMeetingsPaid = refl

trainingNotMeetingWorkload :
  M.trainingHoursEqualGovernanceMeetingHours M.canonicalMondragonCorporationCapacityBoundary ≡ false
trainingNotMeetingWorkload = refl

noTargetTransport :
  M.corporationCapacityEqualsTargetBoloCapacity M.canonicalMondragonCorporationCapacityBoundary ≡ false
noTargetTransport = refl
