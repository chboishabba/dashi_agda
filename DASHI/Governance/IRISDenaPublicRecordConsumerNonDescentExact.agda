module DASHI.Governance.IRISDenaPublicRecordConsumerNonDescentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Governance.IRISDenaPublicRecordCeilingAndFOIExact as Ceiling

------------------------------------------------------------------------
-- PUBLIC IRIS RECORD / EXACT-DUTY NON-DESCENT
--
-- The current public surface distinguishes presence, government's
-- non-offensive position and protocol-governed duty, but not the exact
-- same-episode task.  Two candidate refinements can therefore share the same
-- public surface while differing for an exact-duty consumer.
--
-- This is an epistemic/fibre theorem.  It does NOT assert that both candidate
-- refinements occurred, nor that either is the historical truth.
------------------------------------------------------------------------

data CandidateOperationalState : Set where
  defensiveCandidate : CandidateOperationalState
  maintenanceCandidate : CandidateOperationalState

data PublicSurface : Set where
  presentProtocolGovernedNonOffensive : PublicSurface

data ExactDutyOutcome : Set where
  defensiveOutcome : ExactDutyOutcome
  maintenanceOutcome : ExactDutyOutcome

publicObserver : CandidateOperationalState → PublicSurface
publicObserver defensiveCandidate = presentProtocolGovernedNonOffensive
publicObserver maintenanceCandidate = presentProtocolGovernedNonOffensive

exactDutyConsumer : CandidateOperationalState → ExactDutyOutcome
exactDutyConsumer defensiveCandidate = defensiveOutcome
exactDutyConsumer maintenanceCandidate = maintenanceOutcome

defensiveMaintenanceDiffer :
  exactDutyConsumer defensiveCandidate ≡
  exactDutyConsumer maintenanceCandidate → ⊥
defensiveMaintenanceDiffer ()

publicRecordNonDescent :
  Descent.ConsumerNonDescentWitness publicObserver exactDutyConsumer
publicRecordNonDescent =
  Descent.consumerNonDescentWitness
    defensiveCandidate
    maintenanceCandidate
    refl
    defensiveMaintenanceDiffer

publicRecordCannotBeExactDutySufficient :
  Descent.ConsumerSufficient publicObserver exactDutyConsumer → ⊥
publicRecordCannotBeExactDutySufficient =
  Descent.nonDescentWitnessBlocksSufficiency publicRecordNonDescent

publicRecordCannotFactorExactDuty :
  Descent.FactorsThrough publicObserver exactDutyConsumer → ⊥
publicRecordCannotFactorExactDuty =
  Descent.nonDescentWitnessBlocksFactorization publicRecordNonDescent

publicCeiling : Ceiling.PublicRecordCeiling
publicCeiling = Ceiling.canonicalPublicRecordCeiling

data PublicOpacityProvesEitherCandidateActual : Set where
data NonDescentProvesCovertAction : Set where

data MorePublicStatementsAutomaticallyRepairExactDuty : Set where

opacityDoesNotChooseActualCandidate :
  PublicOpacityProvesEitherCandidateActual → ⊥
opacityDoesNotChooseActualCandidate ()

nonDescentDoesNotProveCovertAction :
  NonDescentProvesCovertAction → ⊥
nonDescentDoesNotProveCovertAction ()

moreStatementsDoNotAutomaticallyRepairExactDuty :
  MorePublicStatementsAutomaticallyRepairExactDuty → ⊥
moreStatementsDoNotAutomaticallyRepairExactDuty ()
