module DASHI.Culture.MissingDeceasedTwentyScientistRound70HCBTaskLevelBoundedExhaustionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistRound66HCBTemporalInstitutionalOverlapExact as R66
import DASHI.Culture.MissingDeceasedTwentyScientistRound67HCBMediaClaimSourceDependenceExact as R67
import DASHI.Culture.MissingDeceasedTwentyScientistRound68HCBDOITechnicalLineageExact as R68
import DASHI.Culture.MissingDeceasedTwentyScientistRound69HCBNamedManagementSurfaceExact as R69

record HCBTaskLevelSearchReceipt : Set where
  constructor hcb-task-level-search-receipt
  field
    searchedPerson : String
    exactProgrammeKeys : String
    searchedCarrierFamilies : String
    positivePrimaryFacts : String
    taskLevelHit : Bool
    boundedScope : String

open HCBTaskLevelSearchReceipt public

mccaslandHCBTaskSearch : HCBTaskLevelSearchReceipt
mccaslandHCBTaskSearch = hcb-task-level-search-receipt
  "William N. McCasland"
  "FA9300-07-C-0001; Hydrocarbon Boost Engine Technology; HBTD; Mondaloy"
  "Air Force biography and heritage; AFRL/AFMC public programme material; SAM.gov exact-contract notice; HCB technical retrospectives; named programme-management surfaces; searched DTIC/DoD/Air Force exact-key web surfaces"
  "McCasland commanded AFRL during part of the active HCB period; HCB and Mondaloy are exact paid programme objects; acquired task-level management surfaces name Robert Bernstein and Joe Burnett rather than McCasland"
  false
  "No identity-bearing McCasland HCB/Mondaloy task, review, funding approval, acquisition decision, contract-management memo, roster or task briefing was located on the declared searched surfaces. This is not an exhaustive archive-wide or classified-record search."

mccaslandTaskLevelHitLocated : Bool
mccaslandTaskLevelHitLocated = false

boundedSearchExhaustedForCurrentSurface : Bool
boundedSearchExhaustedForCurrentSurface = true

boundedNoHitDoesNotPayUniversalNonParticipation : Bool
boundedNoHitDoesNotPayUniversalNonParticipation = true

namedOtherManagersDoesNotProveZeroHigherLevelOversight : Bool
namedOtherManagersDoesNotProveZeroHigherLevelOversight = true

derivativeRepetitionCannotKeepBranchParetoLive : Bool
derivativeRepetitionCannotKeepBranchParetoLive = true

hcbBranchMayYieldUntilNewIdentityLead : Bool
hcbBranchMayYieldUntilNewIdentityLead = true

newIdentityBearingCarrierWouldReopenHCBBranch : Bool
newIdentityBearingCarrierWouldReopenHCBBranch = true

round70H2PaidCount : Nat
round70H2PaidCount = 0

round70H3PaidCount : Nat
round70H3PaidCount = 0

round70Reading : String
round70Reading = "The current claim-indexed public search surface does not locate William N. McCasland on an identity-bearing HCB/Mondaloy task, review, funding, acquisition, contract-management, roster or briefing carrier. Primary records pay AFRL command overlap and exact HCB programme existence, while task-level programme-management surfaces name Robert Bernstein and Joe Burnett. The no-hit is bounded to the searched public surface and cannot prove universal non-participation or absence of higher-level oversight. Under the Pareto scheduler, derivative repetition alone cannot justify continued HCB acquisition spend; the branch yields until a new identity-bearing lead appears."
