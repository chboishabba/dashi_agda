module DASHI.Governance.EmbodiedLossEmergencyMoralUncertaintyExact where

------------------------------------------------------------------------
-- EMBODIED LOSS / EMERGENCY / MORAL UNCERTAINTY
--
-- The generic carrier refuses substrate shortcuts such as human > robot or
-- replaceable hardware -> negligible loss.  Moral-patient evidence, historical
-- continuity, recoverability, mission dependence and relational propagation are
-- independent coordinates.  Emergency override remains separately authorised.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.RepresentationSubjectPositionNonfactorabilityExact
import DASHI.Core.HistoryConditionedChoiceExact
import DASHI.Core.RelationalHistoryFabricExact

------------------------------------------------------------------------
-- Loss coordinates.
------------------------------------------------------------------------

data MoralPatientEvidence : Set where
  noPositiveEvidence uncertainEvidence positiveEvidence : MoralPatientEvidence

data HistoricalContinuity : Set where
  continuityRecoverable continuityPartiallyRecoverable continuityIrrecoverable : HistoricalContinuity

data EmbodimentRecoverability : Set where
  embodimentReplaceable embodimentScarce embodimentUnique : EmbodimentRecoverability

data FunctionalSubstitutability : Set where
  functionSubstitutable functionDelayed functionUnique : FunctionalSubstitutability

data MissionCriticality : Set where
  missionOrdinary missionCritical : MissionCriticality

data RelationalEmbedding : Set where
  relationalLow relationalHigh : RelationalEmbedding

data DownstreamDependence : Set where
  fewDependents manyDependents : DownstreamDependence

data FutureOptionCone : Set where
  narrowFutureCone broadFutureCone : FutureOptionCone

record LossSituation : Set where
  constructor loss-situation
  field
    moralPatient : MoralPatientEvidence
    continuity : HistoricalContinuity
    embodiment : EmbodimentRecoverability
    functionalSubstitution : FunctionalSubstitutability
    mission : MissionCriticality
    relational : RelationalEmbedding
    dependents : DownstreamDependence
    futureCone : FutureOptionCone

------------------------------------------------------------------------
-- Same architecture can carry different histories/relations and therefore
-- different loss situations.
------------------------------------------------------------------------

data Architecture : Set where sameArchitecture : Architecture

data EmbodiedHistory : Set where shallowHistory deepUniqueHistory : EmbodiedHistory

lossFromHistory : Architecture → EmbodiedHistory → LossSituation
lossFromHistory sameArchitecture shallowHistory =
  loss-situation uncertainEvidence continuityRecoverable embodimentReplaceable
    functionSubstitutable missionOrdinary relationalLow fewDependents narrowFutureCone
lossFromHistory sameArchitecture deepUniqueHistory =
  loss-situation uncertainEvidence continuityIrrecoverable embodimentReplaceable
    functionSubstitutable missionCritical relationalHigh manyDependents broadFutureCone

sameArchitectureDifferentHistoryLoss :
  lossFromHistory sameArchitecture shallowHistory
  ≡ lossFromHistory sameArchitecture deepUniqueHistory → ⊥
sameArchitectureDifferentHistoryLoss ()

------------------------------------------------------------------------
-- Non-collapse rules.
------------------------------------------------------------------------

data BackupState : Set where noBackup checkpointAvailable : BackupState

data IdentityPreservation : BackupState → Set where
-- deliberately no generic constructor: a backup does not settle identity

backupDoesNotSettleIdentity : IdentityPreservation checkpointAvailable → ⊥
backupDoesNotSettleIdentity ()

data ReplaceableHardwareClaim : Set where
  hardwareReplaceable : ReplaceableHardwareClaim

data NoMoralSubjectClaim : Set where
  noMoralSubject : NoMoralSubjectClaim

-- No conversion is exposed from replaceable hardware to no-moral-subject claim.

------------------------------------------------------------------------
-- Emergency override requires an independently grounded and proportional bundle.
------------------------------------------------------------------------

data ThreatEvidence : Set where independentlyGroundedThreat : ThreatEvidence

data IrreversibilityEvidence : Set where seriousIrreversibility : IrreversibilityEvidence

data MagnitudeEvidence : Set where seriousMagnitude : MagnitudeEvidence

data Proportionality : Set where proportionateResponse : Proportionality

data LeastHarmAlternative : Set where leastHarmChecked : LeastHarmAlternative

data ExternalOverrideAuthority : Set where externallyGrantedOverride : ExternalOverrideAuthority

record EmergencyOverrideReceipt : Set where
  constructor emergency-override-receipt
  field
    threat : ThreatEvidence
    irreversibility : IrreversibilityEvidence
    magnitude : MagnitudeEvidence
    proportionality : Proportionality
    leastHarm : LeastHarmAlternative
    authority : ExternalOverrideAuthority

canonicalEmergencyOverrideReceipt : EmergencyOverrideReceipt
canonicalEmergencyOverrideReceipt =
  emergency-override-receipt
    independentlyGroundedThreat
    seriousIrreversibility
    seriousMagnitude
    proportionateResponse
    leastHarmChecked
    externallyGrantedOverride

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record EmbodiedLossEmergencyBoundary : Set where
  constructor embodied-loss-emergency-boundary
  field
    substrateLabelDeterminesLossPriority : Bool
    substrateLabelDeterminesLossPriorityIsFalse : substrateLabelDeterminesLossPriority ≡ false
    replaceableHardwareImpliesNoMorallyRelevantSubject : Bool
    replaceableHardwareImpliesNoMorallyRelevantSubjectIsFalse :
      replaceableHardwareImpliesNoMorallyRelevantSubject ≡ false
    backupAvailabilityImpliesIdentityPreserved : Bool
    backupAvailabilityImpliesIdentityPreservedIsFalse : backupAvailabilityImpliesIdentityPreserved ≡ false
    missionCriticalImpliesConscious : Bool
    missionCriticalImpliesConsciousIsFalse : missionCriticalImpliesConscious ≡ false
    consciousImpliesMissionCritical : Bool
    consciousImpliesMissionCriticalIsFalse : consciousImpliesMissionCritical ≡ false
    sameArchitectureImpliesSameLossSituation : Bool
    sameArchitectureImpliesSameLossSituationIsFalse : sameArchitectureImpliesSameLossSituation ≡ false
    selfAssessedEmergencyCreatesOverride : Bool
    selfAssessedEmergencyCreatesOverrideIsFalse : selfAssessedEmergencyCreatesOverride ≡ false
    reading : String

canonicalEmbodiedLossEmergencyBoundary : EmbodiedLossEmergencyBoundary
canonicalEmbodiedLossEmergencyBoundary =
  embodied-loss-emergency-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "Loss is situated across moral-patient evidence, continuity, recoverability, substitutability, mission dependence, relational embedding, dependents and future option cone. Hardware replaceability, backup availability and substrate labels do not settle identity or moral status. Emergency override requires independently grounded threat evidence, proportionality, least-harm analysis and external authority."
