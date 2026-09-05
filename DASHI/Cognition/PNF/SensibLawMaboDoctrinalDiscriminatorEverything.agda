module DASHI.Cognition.PNF.SensibLawMaboDoctrinalDiscriminatorEverything where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityV02Everything as V02
import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityResidualRefinementV02Exact as Refined
import DASHI.Cognition.PNF.SensibLawMaboMinimalDoctrinalDiscriminatorExact as Minimal
import DASHI.Cognition.PNF.SensibLawMaboMinimalDoctrinalHyperfabricBridgeExact as Hyper
import DASHI.Cognition.PNF.SensibLawMaboMinimalDoctrinalCutsetExact as Cutset
import DASHI.Cognition.PNF.SensibLawIssueIndexedAdjudicativeHyperfabricExact as Issue
import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityUseUpgradeExact as Upgrade

------------------------------------------------------------------------
-- Focused capstone: verified primary authority -> four-axis doctrinal
-- discriminator -> claim-specific cutset -> generic issue-hyperfabric work.
------------------------------------------------------------------------

continuityCanCloseNarrowly :
  Cutset.firstResidual Minimal.identifyExistenceContinuity Cutset.postHallVerificationCutset
  ≡ Cutset.minimalDoctrinalClosed
continuityCanCloseNarrowly = refl

extinguishmentCanCloseNarrowly :
  Cutset.firstResidual Minimal.identifyExtinguishmentRule Cutset.postHallVerificationCutset
  ≡ Cutset.minimalDoctrinalClosed
extinguishmentCanCloseNarrowly = refl

recognitionConditionStillOpen :
  Cutset.firstResidual Minimal.identifyRecognitionCondition Cutset.postHallVerificationCutset
  ≡ Cutset.recognitionConditionResidual
recognitionConditionStillOpen = refl

recognitionEvidenceStillOpen :
  Cutset.firstResidual Minimal.identifyRecognitionEvidence Cutset.postHallVerificationCutset
  ≡ Cutset.recognitionEvidenceResidual
recognitionEvidenceStillOpen = refl

unifiedTheoryStopsAtRecognitionCondition :
  Cutset.firstResidual Minimal.identifyUnifiedRecognitionTheory Cutset.postHallVerificationCutset
  ≡ Cutset.recognitionConditionResidual
unifiedTheoryStopsAtRecognitionCondition = refl

------------------------------------------------------------------------
-- Different open fibres compile to different work kinds.
------------------------------------------------------------------------

recognitionConditionNeedsAuthorityWork : Hyper.workKind Hyper.recognitionConditionHyperfabric ≡ Issue.lookWork
recognitionConditionNeedsAuthorityWork = refl
recognitionEvidenceNeedsEvidenceTestWork : Hyper.workKind Hyper.recognitionEvidenceHyperfabric ≡ Issue.testWork
recognitionEvidenceNeedsEvidenceTestWork = refl
unifiedTheoryNeedsSynthesisWork : Hyper.workKind Hyper.unifiedTheoryHyperfabric ≡ Issue.thinkWork
unifiedTheoryNeedsSynthesisWork = refl

------------------------------------------------------------------------
-- Verified Hall/Dawson and Amodu/Brennan-Dawson primary-use seams remain
-- proposition-sensitive.
------------------------------------------------------------------------

verifiedHallDawsonRelationIsContrast :
  Minimal.dawsonRelation Minimal.calderRecognitionAxisContrast ≡ Upgrade.primaryContrastsLaterUse
verifiedHallDawsonRelationIsContrast = refl

amoduContinuityRelationQualifiesDawson :
  Minimal.dawsonRelation Minimal.amoduContinuityAxisContrast ≡ Upgrade.primaryQualifiesLaterUse
amoduContinuityRelationQualifiesDawson = refl

------------------------------------------------------------------------
-- Core non-collapse laws exposed at the capstone surface.
------------------------------------------------------------------------

recognitionEvidenceCannotPayCondition : Minimal.RecognitionEvidenceProvesRecognitionCondition → ⊥
recognitionEvidenceCannotPayCondition = Minimal.evidenceDoesNotProveRecognitionCondition
recognitionConditionCannotPayContinuity : Minimal.RecognitionConditionProvesExistenceContinuity → ⊥
recognitionConditionCannotPayContinuity = Minimal.recognitionConditionDoesNotProveContinuity
continuityCannotPayRecognitionCondition : Minimal.ExistenceContinuityProvesRecognitionCondition → ⊥
continuityCannotPayRecognitionCondition = Minimal.continuityDoesNotProveRecognitionCondition
extinguishmentCannotPayRecognitionEvidence : Cutset.ExtinguishmentClosurePaysRecognitionEvidence → ⊥
extinguishmentCannotPayRecognitionEvidence = Cutset.extinguishmentDoesNotPayRecognitionEvidence
narrowClosureDoesNotRequireUnifiedTheory : Cutset.NarrowClosureRequiresUnifiedTheory → ⊥
narrowClosureDoesNotRequireUnifiedTheory = Cutset.narrowClosureDoesNotRequireUnifiedTheory
oneGlobalDoctrinalCutsetDoesNotFitEveryQuery : Cutset.OneGlobalDoctrinalCutsetFitsEveryQuery → ⊥
oneGlobalDoctrinalCutsetDoesNotFitEveryQuery = Cutset.oneGlobalCutsetDoesNotFitEveryQuery
oneProbeDoesNotFitEveryAxis : Hyper.OneProbeFitsAllMinimalAxes → ⊥
oneProbeDoesNotFitEveryAxis = Hyper.oneProbeDoesNotFitAllAxes

------------------------------------------------------------------------
-- Carry forward the source-authority firewall from the verified v0.2 root.
------------------------------------------------------------------------

authoritativeTextStillDoesNotResolveLegalCoordinate :
  Refined.AuthoritativeTranscriptionMeansCoordinateResolved → ⊥
authoritativeTextStillDoesNotResolveLegalCoordinate = V02.authoritativeTextStillDoesNotResolveCoordinate

exactUnifiedTheoryStillNotClosed :
  Refined.TextNativeAmoduEvidenceResolvesExactMaboTheory → ⊥
exactUnifiedTheoryStillNotClosed = V02.v02DoesNotCloseExactUnifiedTheory
