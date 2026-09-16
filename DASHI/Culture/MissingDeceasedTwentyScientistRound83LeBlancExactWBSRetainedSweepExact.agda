module DASHI.Culture.MissingDeceasedTwentyScientistRound83LeBlancExactWBSRetainedSweepExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ROUND 83 / LEBLANC EXACT-WBS RETAINED-NAME SWEEP
--
-- Search surface: exact key 658133.04.01.22.01.06 crossed against the retained
-- cohort names, plus the acquired NTRS/ANS component and programme carriers.
--
-- Joshua LeBlanc remains the only retained-scientist hit located on this exact
-- WBS surface.  This is bounded to the declared searched/acquired surface and
-- is not a proof that no other retained scientist ever participated elsewhere.
------------------------------------------------------------------------

exactWBS : String
exactWBS = "658133.04.01.22.01.06"

leblancRetainedHitPaid : Bool
leblancRetainedHitPaid = true

secondRetainedHitLocated : Bool
secondRetainedHitLocated = false

boundedNoHitDoesNotPayUniversalAbsence : Bool
boundedNoHitDoesNotPayUniversalAbsence = true

boundedNoHitDoesNotPayNonParticipation : Bool
boundedNoHitDoesNotPayNonParticipation = true

sameWBSNeighbourhoodRemainsDocumented : Bool
sameWBSNeighbourhoodRemainsDocumented = true

branchMayYieldUntilNewExactLead : Bool
branchMayYieldUntilNewExactLead = true

newExactLeadMayReopenBranch : Bool
newExactLeadMayReopenBranch = true

h2Paid : Bool
h2Paid = false

h3Paid : Bool
h3Paid = false

record Round83Boundary : Set where
  constructor round83Boundary
  field
    exactKeyRetainedHitPaid : Bool
    secondRetainedCrossingPaid : Bool
    boundedSearchExhaustionPaid : Bool
    branchYieldable : Bool
    h2PromotionPaid : Bool
    h3PromotionPaid : Bool

canonicalRound83Boundary : Round83Boundary
canonicalRound83Boundary = round83Boundary
  true false true true false false
