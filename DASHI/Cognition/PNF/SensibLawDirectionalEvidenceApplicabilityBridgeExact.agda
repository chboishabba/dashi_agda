module DASHI.Cognition.PNF.SensibLawDirectionalEvidenceApplicabilityBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Algebra.Trit as Trit
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawResolvedLegalEvidenceExact as Evidence
import DASHI.Cognition.PNF.SensibLawApplicabilityPrerequisiteMeetExact as Meet
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Interop.SensibLawNatSourceSupportAcquisitionExact as Source
import DASHI.Interop.SensibLawNatSourcePropositionVerificationExact as Verify

------------------------------------------------------------------------
-- DIRECTIONAL SOURCE EVIDENCE -> EXISTING APPLICABILITY MEET
--
-- This is deliberately a thin weld.  Source proposition verification supplies
-- proposition-relative directional support; the existing SensibLaw legal meet
-- separately owns authority, jurisdiction, scope, event identity, WrongType
-- identity, temporal/exception handling and the semantic legal input gate.
--
-- In particular, a target-claim digest is not definitionally the same object as
-- a semantic proposition reference.  Their correspondence remains an explicit
-- typed receipt rather than a fabricated string equality.
------------------------------------------------------------------------

record SourceTargetLegalPropositionIdentity
    {residual : Source.NatSourceSupportResidual}
    (demand : Verify.SourceVerificationDemand residual)
    {state : Status.SemanticCommitmentState}
    (resolved : Evidence.ResolvedLegalEvidenceReceiptInState state) : Set₁ where
  constructor sourceTargetLegalPropositionIdentity
  field
    observedTargetClaimDigest : String
    observedTargetClaimDigestIsExact :
      observedTargetClaimDigest ≡ Verify.targetClaimDigest demand
    observedSemanticPropositionReference : String
    observedSemanticPropositionReferenceIsExact :
      observedSemanticPropositionReference
      ≡ Status.propositionReference (Evidence.propositionStatus resolved)
    samePropositionAcrossDigestAndSemanticReference : Set
    propositionIdentityReceiptReference : String
open SourceTargetLegalPropositionIdentity public

record PositiveSourceSupportedLegalEvidence
    {residual : Source.NatSourceSupportResidual}
    {demand : Verify.SourceVerificationDemand residual}
    (receipt : Verify.SourceVerificationReceipt demand)
    (admission : Verify.SourceSupportAdmission receipt)
    (state : Status.SemanticCommitmentState) : Set₁ where
  constructor positiveSourceSupportedLegalEvidence
  field
    resolvedLegalEvidence : Evidence.ResolvedLegalEvidenceReceiptInState state
    propositionIdentity :
      SourceTargetLegalPropositionIdentity demand resolvedLegalEvidence
    sourceSupportPaidPositive :
      Verify.sourceSupportPaid admission ≡ true
    directionalSupportPositive :
      Verify.supportTrit admission ≡ Trit.pos
    sourceArtifactAndLegalEvidenceSameObject : Set
    sourceArtifactEvidenceWeldReference : String
open PositiveSourceSupportedLegalEvidence public

record SourceConditionedApplicabilityMeetInput
    {residual : Source.NatSourceSupportResidual}
    {demand : Verify.SourceVerificationDemand residual}
    (receipt : Verify.SourceVerificationReceipt demand)
    (admission : Verify.SourceSupportAdmission receipt)
    (state : Status.SemanticCommitmentState) : Set₁ where
  constructor sourceConditionedApplicabilityMeetInput
  field
    sourceEvidence :
      PositiveSourceSupportedLegalEvidence receipt admission state
    applicabilityInput : Meet.ApplicabilityMeetInput state
    sameResolvedEvidenceUsedByLegalMeet :
      Meet.resolvedEvidence (Meet.prerequisites applicabilityInput)
      ≡ resolvedLegalEvidence sourceEvidence
    bridgeReference : String
open SourceConditionedApplicabilityMeetInput public

compileSourceConditionedApplicability :
  ∀ {residual demand receipt admission state} →
  SourceConditionedApplicabilityMeetInput
    {residual} {demand} receipt admission state →
  Legal.WrongTypeApplicabilityReceipt
compileSourceConditionedApplicability input =
  Meet.compileApplicabilityMeet (applicabilityInput input)

compiledApplicabilityStillComesFromExistingSemanticGate :
  ∀ {residual demand receipt admission state}
    (input : SourceConditionedApplicabilityMeetInput
      {residual} {demand} receipt admission state) →
  Legal.resultingApplicability (compileSourceConditionedApplicability input)
  ≡ Legal.SemanticLegalInputGate.resultingApplicability
      (Meet.semanticInput (applicabilityInput input))
compiledApplicabilityStillComesFromExistingSemanticGate input = refl

------------------------------------------------------------------------
-- FIREWALLS
------------------------------------------------------------------------

data PositiveSourceSupportCreatesLegalAuthority : Set where
data PositiveSourceSupportCreatesJurisdiction : Set where
data PositiveSourceSupportCreatesApplicability : Set where
data DigestIsSemanticReferenceByConstruction : Set where
data SameArtifactMeansSameLegalProposition : Set where

data PositiveSourceSupportCreatesViolation : Set where

data PositiveSourceSupportCreatesLiability : Set where

positiveSourceSupportDoesNotCreateLegalAuthority :
  PositiveSourceSupportCreatesLegalAuthority → ⊥
positiveSourceSupportDoesNotCreateLegalAuthority ()

positiveSourceSupportDoesNotCreateJurisdiction :
  PositiveSourceSupportCreatesJurisdiction → ⊥
positiveSourceSupportDoesNotCreateJurisdiction ()

positiveSourceSupportDoesNotCreateApplicability :
  PositiveSourceSupportCreatesApplicability → ⊥
positiveSourceSupportDoesNotCreateApplicability ()

digestIsNotSemanticReferenceByConstruction :
  DigestIsSemanticReferenceByConstruction → ⊥
digestIsNotSemanticReferenceByConstruction ()

sameArtifactDoesNotMeanSameLegalProposition :
  SameArtifactMeansSameLegalProposition → ⊥
sameArtifactDoesNotMeanSameLegalProposition ()

positiveSourceSupportDoesNotCreateViolation :
  PositiveSourceSupportCreatesViolation → ⊥
positiveSourceSupportDoesNotCreateViolation ()

positiveSourceSupportDoesNotCreateLiability :
  PositiveSourceSupportCreatesLiability → ⊥
positiveSourceSupportDoesNotCreateLiability ()

record DirectionalEvidenceApplicabilityBridgeBoundary : Set where
  constructor directional-evidence-applicability-bridge-boundary
  field
    positiveSourceSupportRequired : Bool
    positiveDirectionalTritRequired : Bool
    propositionIdentityReceiptRequired : Bool
    sourceArtifactEvidenceWeldRequired : Bool
    exactResolvedEvidenceReusedByLegalMeet : Bool
    existingApplicabilityMeetRetained : Bool
    sourceSupportCreatesLegalAuthority : Bool
    sourceSupportCreatesJurisdiction : Bool
    sourceSupportCreatesApplicability : Bool
    digestEqualsSemanticReferenceByConstruction : Bool
    sameArtifactMeansSameLegalProposition : Bool
    sourceSupportCreatesViolation : Bool
    sourceSupportCreatesLiability : Bool

canonicalDirectionalEvidenceApplicabilityBridgeBoundary :
  DirectionalEvidenceApplicabilityBridgeBoundary
canonicalDirectionalEvidenceApplicabilityBridgeBoundary =
  directional-evidence-applicability-bridge-boundary
    true true true true true true
    false false false false false false false
