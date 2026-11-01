module DASHI.Physics.Closure.W3AcceptedEvidenceAuthorityTokenGovernanceObstruction where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataW3NonCollapseWitnessReceipt as NonCollapse
import DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptObligation as EXT
import DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptRequestPack as Pack
import DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate as AUTH
import DASHI.Physics.Closure.W3AcceptedEvidenceAuthorityTokenIntakeRequest as Intake
import DASHI.Physics.Closure.W3AcceptedEvidenceAuthorityTokenReceipt as Receipt

------------------------------------------------------------------------
-- W3 authority-token governance obstruction.
--
-- The landed governance policy permits a later bounded self-issuance receipt
-- for public DOI/frozen-commit evidence, but the current Agda token type is
-- still constructorless.  This module therefore records the exact missing
-- constructor/field instead of promoting W3.

data W3AuthorityGovernancePolicyBranch : Set where
  publicDOIFrozenCommitSelfIssuanceAllowed :
    W3AuthorityGovernancePolicyBranch

data W3AuthorityTokenConstructionStatus : Set where
  blockedByMissingConstructorAndTypedReceipt :
    W3AuthorityTokenConstructionStatus

data W3NonCollapseWitnessRepresentationStatus : Set where
  runnerSideWitnessRepresentedProviderReceiptMissing :
    W3NonCollapseWitnessRepresentationStatus

data W3AuthorityTokenFirstMissingTypedHook : Set where
  missingTokenConstructorOrPolicyHook :
    W3AuthorityTokenFirstMissingTypedHook

record W3AcceptedEvidenceAuthorityTokenGovernanceObstruction : Setω where
  field
    intakeRequest :
      Intake.W3AcceptedEvidenceAuthorityTokenIntakeRequest

    providerResponse :
      Receipt.W3AcceptedEvidenceAuthorityProviderResponse

    currentExternalStatus :
      EXT.W3AcceptedAuthorityExternalReceiptCurrentStatus

    policyDocument :
      String

    selectedPolicyBranch :
      W3AuthorityGovernancePolicyBranch

    policyBranchAllowsBoundedSelfIssuance :
      Bool

    policyBranchAllowsBoundedSelfIssuanceIsTrue :
      policyBranchAllowsBoundedSelfIssuance
      ≡
      true

    tokenConstructionStatus :
      W3AuthorityTokenConstructionStatus

    exactTokenTypeName :
      String

    exactMissingConstructor :
      String

    exactMissingGovernanceHook :
      W3AuthorityTokenFirstMissingTypedHook

    exactMissingGovernanceHookDescription :
      String

    exactDefinitionSitePath :
      String

    exactDefinitionSiteLine :
      Nat

    exactDefinitionSiteForm :
      String

    exactAuthorityBoundaryReceiptShape :
      List String

    exactMissingProviderField :
      Pack.W3AcceptedAuthorityProviderMissingField

    exactMissingProviderFieldIsAuthorityToken :
      exactMissingProviderField
      ≡
      Pack.missingAcceptedEvidenceAuthorityToken

    exactTypedReceiptField :
      String

    typedReceiptConsumesPolicy :
      Bool

    typedReceiptConsumesPolicyIsFalse :
      typedReceiptConsumesPolicy
      ≡
      false

    intakeSelfIssuancePermitted :
      Bool

    intakeSelfIssuancePermittedIsFalse :
      intakeSelfIssuancePermitted
      ≡
      false

    intakeTableChecksumBound :
      Bool

    intakeTableChecksumBoundIsFalse :
      intakeTableChecksumBound
      ≡
      false

    intakeProviderCanonicalTableChecksumBindingPresent :
      Bool

    intakeProviderCanonicalTableChecksumBindingPresentIsFalse :
      intakeProviderCanonicalTableChecksumBindingPresent
      ≡
      false

    authorityTokenConstructed :
      Bool

    authorityTokenConstructedIsFalse :
      authorityTokenConstructed
      ≡
      false

    tokenStillUninhabited :
      AUTH.W3AcceptedEvidenceAuthorityToken →
      ⊥

    externalReceiptStillImpossible :
      EXT.W3AcceptedAuthorityExternalReceipt →
      EXT.W3AcceptedAuthorityExternalReceiptImpossible

    canonicalPayloadsBound :
      Bool

    canonicalPayloadsBoundIsTrue :
      canonicalPayloadsBound
      ≡
      true

    nonCollapseWitnessRepresentation :
      W3NonCollapseWitnessRepresentationStatus

    runnerNonCollapseReceipt :
      NonCollapse.HEPDataW3T43RunnerPerBinNonCollapseReceipt

    runnerNonCollapseStatusIsExtracted :
      NonCollapse.HEPDataW3T43RunnerPerBinNonCollapseReceipt.status
        runnerNonCollapseReceipt
      ≡
      NonCollapse.perBinRunnerWitnessExtracted

    providerGradePayloadRouteHasPayload :
      Bool

    providerGradePayloadRouteHasPayloadIsFalse :
      providerGradePayloadRouteHasPayload
      ≡
      false

    providerGradeNonCollapsePayloadPresent :
      Bool

    providerGradeNonCollapsePayloadPresentIsFalse :
      providerGradeNonCollapsePayloadPresent
      ≡
      false

    exactNonCollapseAssessment :
      List String

    exactActivationRequest :
      List String

    nonPromotionBoundary :
      List String

w3AcceptedEvidenceAuthorityTokenStillUninhabited :
  AUTH.W3AcceptedEvidenceAuthorityToken →
  ⊥
w3AcceptedEvidenceAuthorityTokenStillUninhabited ()

canonicalW3AcceptedEvidenceAuthorityTokenGovernanceObstruction :
  W3AcceptedEvidenceAuthorityTokenGovernanceObstruction
canonicalW3AcceptedEvidenceAuthorityTokenGovernanceObstruction =
  record
    { intakeRequest =
        Intake.canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest
    ; providerResponse =
        Receipt.canonicalW3AcceptedEvidenceAuthorityProviderResponse
    ; currentExternalStatus =
        EXT.currentW3AcceptedAuthorityExternalReceiptStatus
    ; policyDocument =
        "Docs/DASHIGovernanceSelfIssuancePolicy.md"
    ; selectedPolicyBranch =
        publicDOIFrozenCommitSelfIssuanceAllowed
    ; policyBranchAllowsBoundedSelfIssuance =
        true
    ; policyBranchAllowsBoundedSelfIssuanceIsTrue =
        refl
    ; tokenConstructionStatus =
        blockedByMissingConstructorAndTypedReceipt
    ; exactTokenTypeName =
        "DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate.W3AcceptedEvidenceAuthorityToken"
    ; exactMissingConstructor =
        "missing constructor for data W3AcceptedEvidenceAuthorityToken in DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate"
    ; exactMissingGovernanceHook =
        missingTokenConstructorOrPolicyHook
    ; exactMissingGovernanceHookDescription =
        "missing typed self-issuance hook that consumes Docs/DASHIGovernanceSelfIssuancePolicy.md, the canonical t43/t44 payload checksums, the frozen commit, comparison law, runner non-collapse receipt, audit log, revocation clauses, and no-overreach clauses to produce AUTH.W3AcceptedEvidenceAuthorityToken"
    ; exactDefinitionSitePath =
        "DASHI/Physics/Closure/W3AcceptedEmpiricalAuthorityGate.agda"
    ; exactDefinitionSiteLine =
        62
    ; exactDefinitionSiteForm =
        "data W3AcceptedEvidenceAuthorityToken : Set where"
    ; exactAuthorityBoundaryReceiptShape =
        "authorityToken : AUTH.W3AcceptedEvidenceAuthorityToken"
        ∷ "evidenceBackedEmpiricalTarget : AUTH.W3EvidenceBackedEmpiricalTarget"
        ∷ "evidenceTargetCarriesAuthority : evidence-backed target authority == authorityToken"
        ∷ "b4EmpiricalPromotion : W3.B4EmpiricalPromotionObligation"
        ∷ "originReceiptPromotion : W3.OriginReceiptPromotionObligation"
        ∷ "bridgeObligations : W3.W3EmpiricalTargetPromotionBridgeObligations"
        ∷ "bridgeTargetMatchesEvidence : bridge empirical target == evidence-backed empirical target"
        ∷ []
    ; exactMissingProviderField =
        Pack.missingAcceptedEvidenceAuthorityToken
    ; exactMissingProviderFieldIsAuthorityToken =
        refl
    ; exactTypedReceiptField =
        "W3AcceptedEvidenceAuthorityTokenReceipt.authorityToken : AUTH.W3AcceptedEvidenceAuthorityToken"
    ; typedReceiptConsumesPolicy =
        false
    ; typedReceiptConsumesPolicyIsFalse =
        refl
    ; intakeSelfIssuancePermitted =
        Intake.W3AcceptedEvidenceAuthorityTokenIntakeRequest.selfIssuancePermitted
          Intake.canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest
    ; intakeSelfIssuancePermittedIsFalse =
        refl
    ; intakeTableChecksumBound =
        Intake.W3AcceptedEvidenceAuthorityTokenIntakeRequest.tableChecksumBound
          Intake.canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest
    ; intakeTableChecksumBoundIsFalse =
        refl
    ; intakeProviderCanonicalTableChecksumBindingPresent =
        Intake.W3AcceptedEvidenceAuthorityTokenIntakeRequest.providerCanonicalTableChecksumBindingPresent
          Intake.canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest
    ; intakeProviderCanonicalTableChecksumBindingPresentIsFalse =
        refl
    ; authorityTokenConstructed =
        false
    ; authorityTokenConstructedIsFalse =
        refl
    ; tokenStillUninhabited =
        w3AcceptedEvidenceAuthorityTokenStillUninhabited
    ; externalReceiptStillImpossible =
        EXT.currentAcceptedAuthorityExternalReceiptBlockedByAuthority
    ; canonicalPayloadsBound =
        true
    ; canonicalPayloadsBoundIsTrue =
        refl
    ; nonCollapseWitnessRepresentation =
        runnerSideWitnessRepresentedProviderReceiptMissing
    ; runnerNonCollapseReceipt =
        NonCollapse.canonicalHEPDataW3T43RunnerPerBinNonCollapseReceipt
    ; runnerNonCollapseStatusIsExtracted =
        refl
    ; providerGradePayloadRouteHasPayload =
        NonCollapse.HEPDataW3NonCollapseWitnessReceiptRoute.currentRepoHasProviderGradePayload
          NonCollapse.canonicalHEPDataW3NonCollapseWitnessReceiptRoute
    ; providerGradePayloadRouteHasPayloadIsFalse =
        refl
    ; providerGradeNonCollapsePayloadPresent =
        false
    ; providerGradeNonCollapsePayloadPresentIsFalse =
        refl
    ; exactNonCollapseAssessment =
        "The runner-side non-collapse witness is already represented by HEPDataW3T43RunnerPerBinNonCollapseReceipt"
        ∷ "The represented witness is bin 12 with non-zero pull -2.280159308132989 and pred/data distinct"
        ∷ "The canonical intake still records selfIssuancePermitted=false, tableChecksumBound=false, and providerCanonicalTableChecksumBindingPresent=false"
        ∷ "The provider-grade HEPDataExternalNonCollapseWitnessReceipt remains constructorless and absent"
        ∷ "Therefore the witness script is not the first missing item; the missing item is accepted authority/token receipt construction"
        ∷ []
    ; exactActivationRequest =
        "Add an explicit constructor or governance hook for AUTH.W3AcceptedEvidenceAuthorityToken, or provide an external value of that exact type"
        ∷ "Add a typed receipt consuming Docs/DASHIGovernanceSelfIssuancePolicy.md and naming the exact W3 t43/t44 evidence packet"
        ∷ "That receipt must flip the intake-level self-issuance/table-checksum authority fields by construction, not by prose"
        ∷ "Populate W3AcceptedEvidenceAuthorityTokenReceipt.authorityToken with the exact token"
        ∷ "Set Pack.missingAcceptedEvidenceAuthorityToken only after the token field is inhabited"
        ∷ []
    ; nonPromotionBoundary =
        "This obstruction records policy permission plus type-level absence"
        ∷ "No W3AcceptedEvidenceAuthorityToken is constructed"
        ∷ "No W3AcceptedAuthorityExternalReceipt is constructed"
        ∷ "No W3 promotion, W8 origin promotion, W4/W5 promotion, or full unification claim follows"
        ∷ []
    }

canonicalW3AuthorityTokenObstructionStatus :
  W3AcceptedEvidenceAuthorityTokenGovernanceObstruction.tokenConstructionStatus
    canonicalW3AcceptedEvidenceAuthorityTokenGovernanceObstruction
  ≡
  blockedByMissingConstructorAndTypedReceipt
canonicalW3AuthorityTokenObstructionStatus = refl

canonicalW3AuthorityTokenStillUnconstructed :
  W3AcceptedEvidenceAuthorityTokenGovernanceObstruction.authorityTokenConstructed
    canonicalW3AcceptedEvidenceAuthorityTokenGovernanceObstruction
  ≡
  false
canonicalW3AuthorityTokenStillUnconstructed = refl

canonicalW3AuthorityPolicyBranchAllowed :
  W3AcceptedEvidenceAuthorityTokenGovernanceObstruction.policyBranchAllowsBoundedSelfIssuance
    canonicalW3AcceptedEvidenceAuthorityTokenGovernanceObstruction
  ≡
  true
canonicalW3AuthorityPolicyBranchAllowed = refl

canonicalW3AuthorityIntakeSelfIssuanceStillFalse :
  W3AcceptedEvidenceAuthorityTokenGovernanceObstruction.intakeSelfIssuancePermitted
    canonicalW3AcceptedEvidenceAuthorityTokenGovernanceObstruction
  ≡
  false
canonicalW3AuthorityIntakeSelfIssuanceStillFalse = refl

canonicalW3AuthorityIntakeTableChecksumStillFalse :
  W3AcceptedEvidenceAuthorityTokenGovernanceObstruction.intakeTableChecksumBound
    canonicalW3AcceptedEvidenceAuthorityTokenGovernanceObstruction
  ≡
  false
canonicalW3AuthorityIntakeTableChecksumStillFalse = refl

canonicalW3AuthorityProviderCanonicalBindingStillFalse :
  W3AcceptedEvidenceAuthorityTokenGovernanceObstruction.intakeProviderCanonicalTableChecksumBindingPresent
    canonicalW3AcceptedEvidenceAuthorityTokenGovernanceObstruction
  ≡
  false
canonicalW3AuthorityProviderCanonicalBindingStillFalse = refl

canonicalW3RunnerNonCollapseWitnessRepresented :
  W3AcceptedEvidenceAuthorityTokenGovernanceObstruction.runnerNonCollapseStatusIsExtracted
    canonicalW3AcceptedEvidenceAuthorityTokenGovernanceObstruction
  ≡
  refl
canonicalW3RunnerNonCollapseWitnessRepresented = refl

canonicalW3ProviderGradePayloadRouteStillAbsent :
  W3AcceptedEvidenceAuthorityTokenGovernanceObstruction.providerGradePayloadRouteHasPayload
    canonicalW3AcceptedEvidenceAuthorityTokenGovernanceObstruction
  ≡
  false
canonicalW3ProviderGradePayloadRouteStillAbsent = refl

canonicalW3ProviderGradeNonCollapsePayloadAbsent :
  W3AcceptedEvidenceAuthorityTokenGovernanceObstruction.providerGradeNonCollapsePayloadPresent
    canonicalW3AcceptedEvidenceAuthorityTokenGovernanceObstruction
  ≡
  false
canonicalW3ProviderGradeNonCollapsePayloadAbsent = refl
