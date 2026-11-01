module DASHI.Culture.MissingDeceasedTwentyScientistRound65MPTLRetainedNameSweepExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistRound63MPTLAttributedSourceAtlasExact as R63
import DASHI.Culture.MissingDeceasedTwentyScientistRound64DOIFacilityLineageNegativeControlExact as R64

------------------------------------------------------------------------
-- ROUND 65: BOUNDED RETAINED-NAME SWEEP OVER THE EXACT MPTL FAMILY
--
-- The exact public carriers searched are the MPTL BPM report, MPTL ECR,
-- achromat design report, exact MPTL conference title, and the 2025 90-degree
-- achromat publication/index surfaces.  The sweep checks the retained cohort
-- against those exact-object surfaces.  Only Anthony Chavez is located on an
-- exact MPTL carrier in the acquired/search-returned material.
--
-- This is a bounded searched-surface result.  It is NOT a claim that no other
-- retained scientist ever participated in MPTL, DARHT, Scorpius, J-6, LANL,
-- or any non-public/restricted object.
------------------------------------------------------------------------

record RetainedNameSweepReceipt : Set where
  constructor retained-name-sweep-receipt
  field
    retainedName : String
    searchedObjectFamily : String
    exactCarrierHitLocated : Bool
    hitReference : String
    scopeBoundary : String

open RetainedNameSweepReceipt public

chavezSweep : RetainedNameSweepReceipt
chavezSweep = retained-name-sweep-receipt
  "Anthony Chavez / M. Anthony Chavez"
  "LA-UR-24-27763 + LA-UR-24-30822 + LA-UR-22-21508 + IPMHVC P2-29 MPTL + 2025 90-degree achromat publication"
  true
  "LA-UR-24-27763 names M. Anthony Chavez among the authors on the Scorpius and DARHT Multi-Pulse Test Line BPM report"
  "Exact carrier-level hit only; does not transfer Chavez to every MPTL revision or author list."

otherRetainedSweep : RetainedNameSweepReceipt
otherRetainedSweep = retained-name-sweep-receipt
  "the other nineteen retained scientists"
  "exact MPTL title / LA-UR-24-30822 / LA-UR-22-21508 / 2025 achromat title and public indexing/search-returned surfaces"
  false
  "no second retained-name hit returned on the declared searched surfaces"
  "Search-result bounded. Does not prove universal absence from MPTL, DARHT, Scorpius, LANL, unpublished records, restricted records, attendee lists, drawings or other unsearched carriers."

retainedNameSweepCount : Nat
retainedNameSweepCount = 20

mptlExactRetainedHitCount : Nat
mptlExactRetainedHitCount = 1

mptlSecondRetainedPersonLocated : Bool
mptlSecondRetainedPersonLocated = false

boundedNoCrossingDoesNotProveUniversalAbsence : Bool
boundedNoCrossingDoesNotProveUniversalAbsence = true

searchSurfaceAbsenceDoesNotPayNonParticipation : Bool
searchSurfaceAbsenceDoesNotPayNonParticipation = true

exactMPTLAttributionAtlasPreserved : Bool
exactMPTLAttributionAtlasPreserved = true

mptlBranchShouldYieldAfterBoundedSweep : Bool
mptlBranchShouldYieldAfterBoundedSweep = true

newIdentityBearingMPTLLeadMayReopenBranch : Bool
newIdentityBearingMPTLLeadMayReopenBranch = true

round65H2PaidCount : Nat
round65H2PaidCount = 0

round65H3PaidCount : Nat
round65H3PaidCount = 0

round65Reading : String
round65Reading = "A bounded retained-name sweep across the exact public MPTL/BPM/ECR/achromat source family locates Anthony Chavez but no second retained scientist on the acquired/search-returned exact-object surfaces. This narrows the current public crossing search but does not prove universal non-participation. Under the Pareto scheduler, further generic MPTL mining is now dominated unless a new identity-bearing lead, roster, drawing, review record or exact retained-name carrier appears; the critical path should yield to another live H2 residual."
