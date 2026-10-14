module DASHI.Governance.BoloBoloMondragonCorporationGovernanceCapacityExact where

open import DASHI.Core.Prelude

import DASHI.Core.CriticalRelationalGrammarSourceRegistryExact as Registry

------------------------------------------------------------------------
-- MONDRAGON CORPORATION-WIDE GOVERNANCE-CAPACITY EVIDENCE
--
-- Source: MONDRAGON Annual Report 2021 (official corporation report).
--
-- Source-supported coordinates retained here:
--   * 650 representatives from all cooperatives meet annually at Congress;
--   * 665 people were democratically elected members of cooperative governing
--     bodies in the 2021 report;
--   * 11,703 hours of cooperative training were delivered in 2021 to new
--     members and governing bodies;
--   * the extended governance report states that governing bodies such as the
--     Governing Council, Company Council and Deputies Committees meet monthly
--     to monitor management and institutional matters.
--
-- Attribution boundary:
-- these are official MONDRAGON corporate governance/capacity coordinates.
-- They are not p.m./bolo'bolo claims, not university-faculty cadence, not
-- meeting-duration measurements, not interface throughput, and not target-bolo
-- cost/capacity values.  Training hours in particular are capability/education
-- input, not governance-meeting hours.
------------------------------------------------------------------------

mondragonAnnualReport2021Source : Registry.SourceReference
mondragonAnnualReport2021Source = Registry.source-reference
  "MONDRAGON Corporation"
  "Annual Report 2021"
  "official corporate annual report"
  2021
  "https://www.mondragon-corporation.com/people/site/assets/files/103207/annual-report-2021.pdf"
  "official corporate governance/reporting source"
  "source for 650 annual Congress representatives, 665 democratically elected governing-body members, 11,703 cooperative-training hours in 2021, and recurrent governance structures; not a bolo cost or interface-capacity estimate"

record MondragonCorporationGovernanceCapacity : Set where
  constructor mondragon-corporation-governance-capacity
  field
    annualCongressRepresentativeCount : Nat
    annualCongressMeetsAnnually : Bool
    governingBodyMemberCount2021 : Nat
    cooperativeTrainingHours2021 : Nat
    governingBodiesMeetMonthly : Bool

open MondragonCorporationGovernanceCapacity public

canonicalMondragonCorporationGovernanceCapacity :
  MondragonCorporationGovernanceCapacity
canonicalMondragonCorporationGovernanceCapacity =
  mondragon-corporation-governance-capacity
    650 true
    665 11703
    true

record MondragonCorporationCapacityBoundary : Set where
  constructor mondragon-corporation-capacity-boundary
  field
    annualCongressRepresentationPaid : Bool
    governingBodyMembershipPaid : Bool
    cooperativeTrainingInputPaid : Bool
    recurringMonthlyGovernancePaid : Bool
    trainingHoursEqualGovernanceMeetingHours : Bool
    congressRepresentativeCountDeterminesCongressDuration : Bool
    governingBodyCountDeterminesInterfaceCapacity : Bool
    corporationCapacityEqualsUniversityFacultyCadence : Bool
    corporationCapacityEqualsTargetBoloCapacity : Bool
    corporationEvidenceMayConstrainPlausibleFederationDesign : Bool

open MondragonCorporationCapacityBoundary public

canonicalMondragonCorporationCapacityBoundary :
  MondragonCorporationCapacityBoundary
canonicalMondragonCorporationCapacityBoundary =
  mondragon-corporation-capacity-boundary
    true true true true
    false false false false false
    true
