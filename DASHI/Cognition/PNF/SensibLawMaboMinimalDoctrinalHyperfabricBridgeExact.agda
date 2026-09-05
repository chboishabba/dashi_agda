module DASHI.Cognition.PNF.SensibLawMaboMinimalDoctrinalHyperfabricBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawIssueIndexedAdjudicativeHyperfabricExact as Issue
import DASHI.Cognition.PNF.SensibLawMaboBrennanDawsonIssueResidualLiveExact as Mabo
import DASHI.Cognition.PNF.SensibLawMaboMinimalDoctrinalDiscriminatorExact as Minimal

------------------------------------------------------------------------
-- Cross-pollinate the minimal doctrinal discriminator into the generic
-- issue-indexed residual -> obligation -> discriminator -> work-kind shape.
------------------------------------------------------------------------

data MinimalDoctrinalResidual : Set where
  existenceContinuityResidual
  recognitionConditionResidual
  recognitionEvidenceResidual
  extinguishmentResidual
  unifiedTheoryResidual
  doctrinalClosed
  : MinimalDoctrinalResidual

data MinimalProofObligation : Set where
  establishExistenceContinuityRule
  establishRecognitionConditionRule
  establishRecognitionEvidenceBasis
  establishExtinguishmentRule
  reconcileMinimalDoctrine
  noMinimalObligation
  : MinimalProofObligation

data MinimalDiscriminator : Set where
  continuityAuthorityDiscriminator
  recognitionConditionAuthorityDiscriminator
  conductEvidenceDiscriminator
  extinguishmentAuthorityDiscriminator
  crossAxisReconciliationDiscriminator
  noMinimalDiscriminator
  : MinimalDiscriminator

residualForQuery : Minimal.MinimalDoctrinalQuery → MinimalDoctrinalResidual
residualForQuery Minimal.identifyExistenceContinuity = existenceContinuityResidual
residualForQuery Minimal.identifyRecognitionCondition = recognitionConditionResidual
residualForQuery Minimal.identifyRecognitionEvidence = recognitionEvidenceResidual
residualForQuery Minimal.identifyExtinguishmentRule = extinguishmentResidual
residualForQuery Minimal.identifyUnifiedRecognitionTheory = unifiedTheoryResidual

obligationFor : MinimalDoctrinalResidual → MinimalProofObligation
obligationFor existenceContinuityResidual = establishExistenceContinuityRule
obligationFor recognitionConditionResidual = establishRecognitionConditionRule
obligationFor recognitionEvidenceResidual = establishRecognitionEvidenceBasis
obligationFor extinguishmentResidual = establishExtinguishmentRule
obligationFor unifiedTheoryResidual = reconcileMinimalDoctrine
obligationFor doctrinalClosed = noMinimalObligation

discriminatorFor : MinimalProofObligation → MinimalDiscriminator
discriminatorFor establishExistenceContinuityRule = continuityAuthorityDiscriminator
discriminatorFor establishRecognitionConditionRule = recognitionConditionAuthorityDiscriminator
discriminatorFor establishRecognitionEvidenceBasis = conductEvidenceDiscriminator
discriminatorFor establishExtinguishmentRule = extinguishmentAuthorityDiscriminator
discriminatorFor reconcileMinimalDoctrine = crossAxisReconciliationDiscriminator
discriminatorFor noMinimalObligation = noMinimalDiscriminator

workKindFor : MinimalDiscriminator → Issue.EpistemicWorkKind
workKindFor continuityAuthorityDiscriminator = Issue.lookWork
workKindFor recognitionConditionAuthorityDiscriminator = Issue.lookWork
workKindFor conductEvidenceDiscriminator = Issue.testWork
workKindFor extinguishmentAuthorityDiscriminator = Issue.lookWork
workKindFor crossAxisReconciliationDiscriminator = Issue.thinkWork
workKindFor noMinimalDiscriminator = Issue.noWork

record MinimalDoctrineHyperfabricReceipt : Set where
  constructor minimalDoctrineHyperfabricReceipt
  field
    issue : Issue.LegalIssue
    query : Minimal.MinimalDoctrinalQuery
    residual : MinimalDoctrinalResidual
    residualExact : residual ≡ residualForQuery query
    obligation : MinimalProofObligation
    obligationExact : obligation ≡ obligationFor residual
    discriminator : MinimalDiscriminator
    discriminatorExact : discriminator ≡ discriminatorFor obligation
    workKind : Issue.EpistemicWorkKind
    workKindExact : workKind ≡ workKindFor discriminator
    issueIdentityPreserved : issue ≡ Mabo.maboRecognitionIssue
    compilationReference : String
open MinimalDoctrineHyperfabricReceipt public

compileMinimalQuery : Minimal.MinimalDoctrinalQuery → MinimalDoctrineHyperfabricReceipt
compileMinimalQuery query = minimalDoctrineHyperfabricReceipt
  Mabo.maboRecognitionIssue
  query
  (residualForQuery query) refl
  (obligationFor (residualForQuery query)) refl
  (discriminatorFor (obligationFor (residualForQuery query))) refl
  (workKindFor (discriminatorFor (obligationFor (residualForQuery query)))) refl
  refl
  "minimal Mabo doctrine query -> exact residual -> proof obligation -> discriminator -> epistemic work kind"

continuityHyperfabric : MinimalDoctrineHyperfabricReceipt
continuityHyperfabric = compileMinimalQuery Minimal.identifyExistenceContinuity
recognitionConditionHyperfabric : MinimalDoctrineHyperfabricReceipt
recognitionConditionHyperfabric = compileMinimalQuery Minimal.identifyRecognitionCondition
recognitionEvidenceHyperfabric : MinimalDoctrineHyperfabricReceipt
recognitionEvidenceHyperfabric = compileMinimalQuery Minimal.identifyRecognitionEvidence
extinguishmentHyperfabric : MinimalDoctrineHyperfabricReceipt
extinguishmentHyperfabric = compileMinimalQuery Minimal.identifyExtinguishmentRule
unifiedTheoryHyperfabric : MinimalDoctrineHyperfabricReceipt
unifiedTheoryHyperfabric = compileMinimalQuery Minimal.identifyUnifiedRecognitionTheory

continuityUsesAuthorityLook : workKind continuityHyperfabric ≡ Issue.lookWork
continuityUsesAuthorityLook = refl
recognitionConditionUsesAuthorityLook : workKind recognitionConditionHyperfabric ≡ Issue.lookWork
recognitionConditionUsesAuthorityLook = refl
recognitionEvidenceUsesTestWork : workKind recognitionEvidenceHyperfabric ≡ Issue.testWork
recognitionEvidenceUsesTestWork = refl
extinguishmentUsesAuthorityLook : workKind extinguishmentHyperfabric ≡ Issue.lookWork
extinguishmentUsesAuthorityLook = refl
unifiedTheoryUsesThinkWork : workKind unifiedTheoryHyperfabric ≡ Issue.thinkWork
unifiedTheoryUsesThinkWork = refl

recognitionConditionObligationDiffersFromEvidence :
  obligation recognitionConditionHyperfabric ≡ establishRecognitionConditionRule
recognitionConditionObligationDiffersFromEvidence = refl
recognitionEvidenceObligationIsEvidenceSpecific :
  obligation recognitionEvidenceHyperfabric ≡ establishRecognitionEvidenceBasis
recognitionEvidenceObligationIsEvidenceSpecific = refl

data RecognitionEvidenceMayPayRecognitionCondition : Set where
data RecognitionConditionMayPayRecognitionEvidence : Set where
data OneProbeFitsAllMinimalAxes : Set where
data MinimalBridgeChangesIssueIdentity : Set where
data MinimalBridgeAdjudicatesFinalDoctrine : Set where

evidenceDoesNotPayCondition : RecognitionEvidenceMayPayRecognitionCondition → ⊥
evidenceDoesNotPayCondition ()
conditionDoesNotPayEvidence : RecognitionConditionMayPayRecognitionEvidence → ⊥
conditionDoesNotPayEvidence ()
oneProbeDoesNotFitAllAxes : OneProbeFitsAllMinimalAxes → ⊥
oneProbeDoesNotFitAllAxes ()
minimalBridgePreservesIssue : MinimalBridgeChangesIssueIdentity → ⊥
minimalBridgePreservesIssue ()
minimalBridgeDoesNotAdjudicateDoctrine : MinimalBridgeAdjudicatesFinalDoctrine → ⊥
minimalBridgeDoesNotAdjudicateDoctrine ()
