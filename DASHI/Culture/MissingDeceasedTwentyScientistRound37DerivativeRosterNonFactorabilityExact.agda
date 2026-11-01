module DASHI.Culture.MissingDeceasedTwentyScientistRound37DerivativeRosterNonFactorabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Culture.MissingDeceasedTwentyScientistRound36HCBContractDerivativeIdentityExact as R36

------------------------------------------------------------------------
-- ROUND 37: DERIVATIVE-ROSTER NON-FACTORABILITY
--
-- Round 36 exposes a real but partial person-bearing surface: currently
-- acquired patents/derivatives tied to FA9300-07-C-0001 name Pelfrey,
-- Pinera and Huber.  The live query, however, is whether a particular person
-- held some exact HCB contract/task role.  A partial inventor surface cannot
-- decide that query merely from absence.
------------------------------------------------------------------------

data ContractRoleWorld : Set where
  roleExistsOutsideCurrentDerivatives : ContractRoleWorld
  noSuchRoleInWorld : ContractRoleWorld

data CurrentDerivativeRosterObservation : Set where
  currentDerivativeRoster : CurrentDerivativeRosterObservation

data ExactRoleQuery : Set where
  hasExactContractRole : ExactRoleQuery

data ExactRoleAnswer : Set where
  yesExactRole noExactRole : ExactRoleAnswer

projectCurrentDerivativeRoster : ContractRoleWorld → CurrentDerivativeRosterObservation
projectCurrentDerivativeRoster _ = currentDerivativeRoster

answerExactRole : ExactRoleQuery → ContractRoleWorld → ExactRoleAnswer
answerExactRole hasExactContractRole roleExistsOutsideCurrentDerivatives = yesExactRole
answerExactRole hasExactContractRole noSuchRoleInWorld = noExactRole

exactRoleSemantics : Query.QuerySemantics ContractRoleWorld ExactRoleQuery ExactRoleAnswer
exactRoleSemantics = Query.querySemantics answerExactRole

derivativeRosterQueryDefect :
  Query.QueryAdequacyDefect
    projectCurrentDerivativeRoster
    exactRoleSemantics
    hasExactContractRole
derivativeRosterQueryDefect =
  Query.queryAdequacyDefect
    roleExistsOutsideCurrentDerivatives
    noSuchRoleInWorld
    refl
    (λ ())

derivativeRosterCannotDetermineExactRole :
  Query.AdequateFor
    projectCurrentDerivativeRoster
    exactRoleSemantics
    hasExactContractRole →
  ⊥
derivativeRosterCannotDetermineExactRole =
  Query.queryAdequacyDefectBlocksFactorisation derivativeRosterQueryDefect

round37UsesRound36ContractIdentifier : Bool
round37UsesRound36ContractIdentifier = true

currentDerivativeRosterAbsenceCannotPayNonParticipation : Bool
currentDerivativeRosterAbsenceCannotPayNonParticipation = true

namedDerivativeParticipantDoesNotImplyExhaustiveRoster : Bool
namedDerivativeParticipantDoesNotImplyExhaustiveRoster = true

syntheticCollisionDoesNotAssertHistoricalParticipation : Bool
syntheticCollisionDoesNotAssertHistoricalParticipation = true

identityBearingExactRoleReceiptRepairsDefect : Bool
identityBearingExactRoleReceiptRepairsDefect = true

round37H2PaidCount : Nat
round37H2PaidCount = 0

round37H3PaidCount : Nat
round37H3PaidCount = 0

round37Pareto : String
round37Pareto = "Use FA9300-07-C-0001 as a snowball key into additional contemporaneous patents, papers, contract modifications, programme reviews, attendee/distribution records and approval chains. Current derivative inventor absence is not evidence of non-participation; only a positive identity-bearing exact-role source can pay the live McCasland task-role debt."
