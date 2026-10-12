module DASHI.Governance.IRISDenaObserverHierarchyNonDescentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Governance.IRISDenaPublicRecordConsumerNonDescentExact as Public

------------------------------------------------------------------------
-- IRIS EVIDENCE OBSERVER HIERARCHY
--
-- Public record < duty class / protocol < exact same-episode task.
-- Paying a coarser acquisition cell cannot automatically pay a finer one.
------------------------------------------------------------------------

data RefinedOperationalState : Set where
  electricalMaintenanceCandidate : RefinedOperationalState
  mechanicalMaintenanceCandidate : RefinedOperationalState

data DutyClassSurface : Set where
  platformMaintenanceClass : DutyClassSurface

data ProtocolSurface : Set where
  lawfulProtocolGovernedMaintenance : ProtocolSurface

data ExactTask : Set where
  electricalTask : ExactTask
  mechanicalTask : ExactTask

dutyClassObserver : RefinedOperationalState → DutyClassSurface
dutyClassObserver electricalMaintenanceCandidate = platformMaintenanceClass
dutyClassObserver mechanicalMaintenanceCandidate = platformMaintenanceClass

protocolObserver : RefinedOperationalState → ProtocolSurface
protocolObserver electricalMaintenanceCandidate = lawfulProtocolGovernedMaintenance
protocolObserver mechanicalMaintenanceCandidate = lawfulProtocolGovernedMaintenance

exactTaskConsumer : RefinedOperationalState → ExactTask
exactTaskConsumer electricalMaintenanceCandidate = electricalTask
exactTaskConsumer mechanicalMaintenanceCandidate = mechanicalTask

electricalMechanicalDiffer :
  exactTaskConsumer electricalMaintenanceCandidate ≡
  exactTaskConsumer mechanicalMaintenanceCandidate → ⊥
electricalMechanicalDiffer ()

dutyClassNonDescent :
  Descent.ConsumerNonDescentWitness dutyClassObserver exactTaskConsumer
dutyClassNonDescent =
  Descent.consumerNonDescentWitness
    electricalMaintenanceCandidate
    mechanicalMaintenanceCandidate
    refl
    electricalMechanicalDiffer

protocolNonDescent :
  Descent.ConsumerNonDescentWitness protocolObserver exactTaskConsumer
protocolNonDescent =
  Descent.consumerNonDescentWitness
    electricalMaintenanceCandidate
    mechanicalMaintenanceCandidate
    refl
    electricalMechanicalDiffer

verifiedDutyClassCannotSubstituteExactTask :
  Descent.FactorsThrough dutyClassObserver exactTaskConsumer → ⊥
verifiedDutyClassCannotSubstituteExactTask =
  Descent.nonDescentWitnessBlocksFactorization dutyClassNonDescent

completeProtocolCannotSubstituteExactTask :
  Descent.FactorsThrough protocolObserver exactTaskConsumer → ⊥
completeProtocolCannotSubstituteExactTask =
  Descent.nonDescentWitnessBlocksFactorization protocolNonDescent

publicRecordNonDescent :
  Descent.ConsumerNonDescentWitness
    Public.publicObserver
    Public.exactDutyConsumer
publicRecordNonDescent = Public.publicRecordNonDescent

data HansardPaymentDeletesOperationalResidual : Set where
data ProtocolPaymentDeletesOperationalResidual : Set where
data ObserverHierarchyRanksSourceAuthority : Set where

hansardPaymentDoesNotDeleteOperationalResidual :
  HansardPaymentDeletesOperationalResidual → ⊥
hansardPaymentDoesNotDeleteOperationalResidual ()

protocolPaymentDoesNotDeleteOperationalResidual :
  ProtocolPaymentDeletesOperationalResidual → ⊥
protocolPaymentDoesNotDeleteOperationalResidual ()

observerHierarchyDoesNotRankAuthority :
  ObserverHierarchyRanksSourceAuthority → ⊥
observerHierarchyDoesNotRankAuthority ()
