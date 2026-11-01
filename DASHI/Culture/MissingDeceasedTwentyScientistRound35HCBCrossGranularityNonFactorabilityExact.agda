module DASHI.Culture.MissingDeceasedTwentyScientistRound35HCBCrossGranularityNonFactorabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Culture.MissingDeceasedTwentyScientistRound32MonicaHCBRolePaymentExact as R32
import DASHI.Culture.MissingDeceasedTwentyScientistRound34McCaslandHCBPublicReferenceExact as R34

------------------------------------------------------------------------
-- ROUND 35: HCB CROSS-GRANULARITY NON-FACTORABILITY
--
-- The acquired source surface pays two HCB relations at different levels:
-- one exact project relation and one programme-level public reference.
-- This module records that those observations do not determine whether both
-- people held roles on the same exact task or contract.
------------------------------------------------------------------------

record HCBCrossGranularityPaidSurface : Set where
  constructor hcb-cross-granularity-paid-surface
  field
    monicaObjectReceipt : R32.MonicaHCBRoleReceipt
    mccaslandProgrammeReceipt : R34.McCaslandHCBPublicReferenceReceipt
    monicaExactHCBObjectRolePaid : Bool
    mccaslandHCBProgrammeReferencePaid : Bool
    mccaslandExactTaskRolePaid : Bool
    crossPersonSameTaskPaid : Bool
    interpretation : String

open HCBCrossGranularityPaidSurface public

currentPaidSurface : HCBCrossGranularityPaidSurface
currentPaidSurface = hcb-cross-granularity-paid-surface
  R32.round32Receipt
  R34.round34Receipt
  true
  true
  false
  false
  "One exact HCB/Mondaloy project relation and one HCB programme-level public reference are paid. No acquired source places both people on the same exact task, contract role, or materials work package."

monicaExactHCBObjectRolePaid : Bool
monicaExactHCBObjectRolePaid = true

mccaslandHCBProgrammeReferencePaid : Bool
mccaslandHCBProgrammeReferencePaid = true

mccaslandExactTaskRolePaid : Bool
mccaslandExactTaskRolePaid = false

crossPersonSameTaskPaid : Bool
crossPersonSameTaskPaid = false

data HCBRoleWorld : Set where
  sameTaskWorld differentTaskWorld : HCBRoleWorld

data PaidCrossGranularityObservation : Set where
  objectPlusProgrammeReference : PaidCrossGranularityObservation

data SameTaskQuery : Set where
  shareExactTask : SameTaskQuery

data SameTaskAnswer : Set where
  yesSameTask noSameTask : SameTaskAnswer

projectPaidCrossGranularity : HCBRoleWorld → PaidCrossGranularityObservation
projectPaidCrossGranularity _ = objectPlusProgrammeReference

answerSameTask : SameTaskQuery → HCBRoleWorld → SameTaskAnswer
answerSameTask shareExactTask sameTaskWorld = yesSameTask
answerSameTask shareExactTask differentTaskWorld = noSameTask

sameTaskSemantics : Query.QuerySemantics HCBRoleWorld SameTaskQuery SameTaskAnswer
sameTaskSemantics = Query.querySemantics answerSameTask

hcbCrossGranularityQueryDefect :
  Query.QueryAdequacyDefect
    projectPaidCrossGranularity
    sameTaskSemantics
    shareExactTask
hcbCrossGranularityQueryDefect =
  Query.queryAdequacyDefect
    sameTaskWorld
    differentTaskWorld
    refl
    (λ ())

paidCrossGranularitySurfaceCannotDetermineSameTask :
  Query.AdequateFor
    projectPaidCrossGranularity
    sameTaskSemantics
    shareExactTask →
  ⊥
paidCrossGranularitySurfaceCannotDetermineSameTask =
  Query.queryAdequacyDefectBlocksFactorisation hcbCrossGranularityQueryDefect

programmeReferenceCannotLiftToTaskRole : Bool
programmeReferenceCannotLiftToTaskRole = true

oneExactRolePlusOneProgrammeReferenceCannotPayH2 : Bool
oneExactRolePlusOneProgrammeReferenceCannotPayH2 = true

syntheticCollisionDoesNotAssertHistoricalSameTask : Bool
syntheticCollisionDoesNotAssertHistoricalSameTask = true

identityBearingTaskReceiptRepairsDefect : Bool
identityBearingTaskReceiptRepairsDefect = true

round35H2PaidCount : Nat
round35H2PaidCount = 0

round35H3PaidCount : Nat
round35H3PaidCount = 0

round35Pareto : String
round35Pareto = "The remaining granularity mismatch is exact-project relation versus programme-level reference. Resolve it only with an identity-bearing exact-task or contract-role source such as a contract modification, attendee/distribution record, programme-review approval chain, or proceedings roster."
