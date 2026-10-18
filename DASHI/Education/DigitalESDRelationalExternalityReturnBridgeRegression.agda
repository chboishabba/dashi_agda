module DASHI.Education.DigitalESDRelationalExternalityReturnBridgeRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Education.DigitalESDRelationalExternalityReturnBridgeExact as Bridge
import DASHI.Education.EducationSituatedInvestmentTrajectoryExact as Trajectory
import DASHI.Governance.DecisionContestedAuthorityJusticeConvergenceExact as Politics
import DASHI.Education.DigitalESDExternalityIncidenceAuditExact as Incidence
import DASHI.Education.DigitalESDInstitutionalDurabilityMaintenanceExact as Durability
import DASHI.Education.AliceBrownDigitalESDEpistemicGovernanceBridgeExact as Alice

sameReturnAutonomyStillBlocked :
  INF.FactorsThrough Trajectory.returnObserver Trajectory.revisionAutonomy → ⊥
sameReturnAutonomyStillBlocked = Bridge.sameReturnCannotRecoverAutonomy

sameReturnBurdenStillBlocked :
  INF.FactorsThrough Trajectory.returnObserver Trajectory.burdenState → ⊥
sameReturnBurdenStillBlocked = Bridge.sameReturnCannotRecoverBurden

sameReturnVoiceStillBlocked :
  INF.FactorsThrough Trajectory.returnObserver Trajectory.voiceState → ⊥
sameReturnVoiceStillBlocked = Bridge.sameReturnCannotRecoverVoice

politicalFineStateStillNotRecoverable :
  INF.FactorsThrough
    Politics.institutionalSurface
    Politics.fineInstitutionalStateOf
  → ⊥
politicalFineStateStillNotRecoverable =
  Bridge.institutionalSurfaceCannotRecoverPoliticalFineState

externalityOwnerRegression :
  Bridge.canonicalExternalityBoundary
  ≡ Incidence.canonicalExternalityIncidenceBoundary
externalityOwnerRegression = refl

durabilityOwnerRegression :
  Bridge.canonicalDurabilityBoundary
  ≡ Durability.canonicalInstitutionalDurabilityBoundary
durabilityOwnerRegression = refl

aliceOwnerRegression :
  Bridge.canonicalAliceBoundary
  ≡ Alice.canonicalAliceBrownDigitalESDEpistemicGovernanceBridge
aliceOwnerRegression = refl

trajectoryOwnerRegression :
  Bridge.canonicalTrajectoryBoundary
  ≡ Trajectory.canonicalSituatedInvestmentTrajectoryBoundary
trajectoryOwnerRegression = refl

returnDoesNotDiagnoseTrauma :
  Bridge.EconomicReturnCreatesTraumaDiagnosis → ⊥
returnDoesNotDiagnoseTrauma =
  Bridge.economicReturnDoesNotCreateTraumaDiagnosis

memoryDoesNotDeterminePolitics :
  Bridge.MemoryStateDeterminesPoliticalPreference → ⊥
memoryDoesNotDeterminePolitics =
  Bridge.memoryStateDoesNotDeterminePoliticalPreference

quietDoesNotCloseJustice :
  Bridge.InstitutionalQuietCreatesJusticeClosure → ⊥
quietDoesNotCloseJustice =
  Bridge.institutionalQuietDoesNotCreateJusticeClosure
