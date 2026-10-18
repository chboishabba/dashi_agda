module DASHI.Education.DigitalESDSourceAuditScaleRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDSourceAuditScaleExact as Audit

score0Pinned : Audit.Score0to5
score0Pinned = Audit.score0Absent

score1Pinned : Audit.Score0to5
score1Pinned = Audit.score1Mentioned

score2Pinned : Audit.Score0to5
score2Pinned = Audit.score2Indirect

score3Pinned : Audit.Score0to5
score3Pinned = Audit.score3DirectIncomplete

score4Pinned : Audit.Score0to5
score4Pinned = Audit.score4Substantial

score5Pinned : Audit.Score0to5
score5Pinned = Audit.score5UnusuallyComplete

educationAxisPinned : Audit.CoreAuditAxis
educationAxisPinned = Audit.educationalOutcomeTransformation

representationAxisPinned : Audit.CoreAuditAxis
representationAxisPinned = Audit.representationWhoMissing

disabilityAxisPinned : Audit.CoreAuditAxis
disabilityAxisPinned = Audit.disabilityEffectiveAccessibility

participantAxisPinned : Audit.CoreAuditAxis
participantAxisPinned = Audit.participantVoiceAuthority

environmentAxisPinned : Audit.CoreAuditAxis
environmentAxisPinned = Audit.environmentalMaterialLifecycle

externalityAxisPinned : Audit.CoreAuditAxis
externalityAxisPinned = Audit.externalityIncidence

politicalEconomyAxisPinned : Audit.CoreAuditAxis
politicalEconomyAxisPinned = Audit.politicalEconomy

socialProvisionAxisPinned : Audit.CoreAuditAxis
socialProvisionAxisPinned = Audit.socialProvisioningCommunity

durabilityAxisPinned : Audit.CoreAuditAxis
durabilityAxisPinned = Audit.maintenanceInstitutionalDurability

contextAxisPinned : Audit.CoreAuditAxis
contextAxisPinned = Audit.contextTransferTimeIntergenerational

scoreCannotCreateQualityPinned : Audit.ScoreCreatesSourceQuality → ⊥
scoreCannotCreateQualityPinned = Audit.scoreDoesNotCreateSourceQuality

scoreCannotRaiseClaimCeilingPinned : Audit.ScoreRaisesClaimCeiling → ⊥
scoreCannotRaiseClaimCeilingPinned = Audit.scoreDoesNotRaiseClaimCeiling
