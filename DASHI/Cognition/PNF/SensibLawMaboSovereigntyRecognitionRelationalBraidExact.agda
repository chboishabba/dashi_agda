module DASHI.Cognition.PNF.SensibLawMaboSovereigntyRecognitionRelationalBraidExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboMinimalDoctrinalDiscriminatorExact as Minimal
import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityPropositionWeldExact as Primary
import DASHI.Cognition.PNF.SensibLawCalderAuthoritativeTranscriptionVerificationExact as Verify
import DASHI.Governance.AuthorityMandateCore as Authority
import DASHI.Governance.RevolutionaryPracticeBraid as Braid

------------------------------------------------------------------------
-- Cross-domain braid for sovereignty/recognition language.
--
-- This file does NOT import governance or Sweetgrass material as Native Title
-- doctrine.  It reuses generic non-collapse boundaries only where an explicit
-- bridge receipt says that the formal shape is analogous.
------------------------------------------------------------------------

data SovereigntyTransitionKind : Set where
  mereChangeOfSovereignty
  rightsAlteringJuridicalAct
  expressExtinguishmentAct
  inconsistentGrantOrAppropriation
  : SovereigntyTransitionKind

data RightsEffect : Set where
  continuityNotDisplacedByTransitionAlone
  rightsAlterationRequiresFurtherJuridicalBasis
  extinguishmentCandidate
  : RightsEffect

transitionEffect : SovereigntyTransitionKind → RightsEffect
transitionEffect mereChangeOfSovereignty = continuityNotDisplacedByTransitionAlone
transitionEffect rightsAlteringJuridicalAct = rightsAlterationRequiresFurtherJuridicalBasis
transitionEffect expressExtinguishmentAct = extinguishmentCandidate
transitionEffect inconsistentGrantOrAppropriation = extinguishmentCandidate

mereChangeDoesNotEncodeExtinguishment :
  transitionEffect mereChangeOfSovereignty ≡ continuityNotDisplacedByTransitionAlone
mereChangeDoesNotEncodeExtinguishment = refl

record MereSovereigntyTransitionBoundary : Set where
  constructor mereSovereigntyTransitionBoundary
  field
    transitionReference : String
    sovereigntyStatusChanges : Bool
    sovereigntyStatusChangesIsTrue : sovereigntyStatusChanges ≡ true
    extinguishmentFollowsFromTransitionAlone : Bool
    extinguishmentFollowsFromTransitionAloneIsFalse : extinguishmentFollowsFromTransitionAlone ≡ false
    allLegalRelationsRemainUnchanged : Bool
    allLegalRelationsRemainUnchangedIsFalse : allLegalRelationsRemainUnchanged ≡ false
    furtherJuridicalActMayAlterRights : Bool
    furtherJuridicalActMayAlterRightsIsTrue : furtherJuridicalActMayAlterRights ≡ true
open MereSovereigntyTransitionBoundary public

maboMereSovereigntyBoundary : MereSovereigntyTransitionBoundary
maboMereSovereigntyBoundary = mereSovereigntyTransitionBoundary
  "Mabo continuity boundary: mere change/acquisition of sovereignty is separated from a distinct rights-altering or extinguishing juridical act"
  true refl false refl false refl true refl

------------------------------------------------------------------------
-- Generic recognition/source distinction.
------------------------------------------------------------------------

data RecognitionRole : Set where
  recognitionAsConstitutiveCondition
  recognitionAsEvidence
  recognitionAsExternalAcknowledgement
  recognitionAsSourceOfAuthority
  : RecognitionRole

data EntitlementSourceRole : Set where
  antecedentCommunityLawOrCustom
  crownOrStateGrant
  delegatedPublicMandate
  sourceUnresolved
  : EntitlementSourceRole

record RecognitionCreationFirewall : Set where
  constructor recognitionCreationFirewall
  field
    recognitionRole : RecognitionRole
    sourceRole : EntitlementSourceRole
    recognitionCreatesObject : Bool
    recognitionCreatesObjectIsFalse : recognitionCreatesObject ≡ false
    recognitionMayAffectLegalEnforceabilityOrProof : Bool
    recognitionMayAffectLegalEnforceabilityOrProofIsTrue : recognitionMayAffectLegalEnforceabilityOrProof ≡ true
    bridgeReference : String
open RecognitionCreationFirewall public

nativeTitleRecognitionFirewall : RecognitionCreationFirewall
nativeTitleRecognitionFirewall = recognitionCreationFirewall
  recognitionAsEvidence antecedentCommunityLawOrCustom false refl true refl
  "cross-domain formal firewall only: recognition may bear on proof/enforceability without being encoded as the source that creates the antecedent right"

------------------------------------------------------------------------
-- Explicit cross-domain bridge receipts.
------------------------------------------------------------------------

data BridgeKind : Set where
  shapeOnlyAnalogy
  noSemanticAuthorityTransport
  : BridgeKind

record CrossDomainRecognitionBridge : Set where
  constructor crossDomainRecognitionBridge
  field
    sourceDomain targetDomain : String
    sourceBoundaryReference targetBoundaryReference : String
    bridgeKind : BridgeKind
    sourceDoctrineImportedAsTargetDoctrine : Bool
    sourceDoctrineImportedAsTargetDoctrineIsFalse : sourceDoctrineImportedAsTargetDoctrine ≡ false
    sharedFormalBoundary : String
open CrossDomainRecognitionBridge public

governanceRecognitionBridge : CrossDomainRecognitionBridge
governanceRecognitionBridge = crossDomainRecognitionBridge
  "DASHI.Governance.AuthorityMandateCore"
  "SensibLaw Mabo/Native Title recognition discriminator"
  "externalRecognitionAloneRejected"
  "RecognitionCondition != RecognitionEvidence != source of antecedent right"
  shapeOnlyAnalogy
  false refl
  "recognition/acknowledgement alone is not automatically the originating source of the underlying authority/right object"

sweetgrassRelationalBridge : CrossDomainRecognitionBridge
sweetgrassRelationalBridge = crossDomainRecognitionBridge
  "DASHI.Governance.RevolutionaryPracticeBraid / Sweetgrass carrier"
  "SensibLaw Mabo/Native Title relational source-boundary audit"
  "distinct strands; reciprocity/affected voice; no legal authority promotion"
  "legal source attribution and affected-community relational context remain distinct from doctrinal holding authority"
  noSemanticAuthorityTransport
  false refl
  "braiding preserves distinct institutional, relational, epistemic, ecological and historical strands; it does not collapse traditions or create legal authority"

------------------------------------------------------------------------
-- Existing repository boundaries are inherited as cross-checks only.
------------------------------------------------------------------------

governanceExternalRecognitionAloneRejected :
  Authority.AdmissibleAuthoritySource Authority.externalRecognitionAlone → Authority.Never
governanceExternalRecognitionAloneRejected = Authority.externalRecognitionAloneRejected

governanceDelegationDoesNotAlienateConstituency :
  Authority.delegationAlienatesConstituencySovereignty Authority.canonicalMandateAuthorityBoundary ≡ false
governanceDelegationDoesNotAlienateConstituency = refl

braidRetainsDistinctStrands :
  Braid.braidRetainsDistinctStrands Braid.canonicalRevolutionaryPracticeBraidSurface ≡ true
braidRetainsDistinctStrands = refl

braidDoesNotCreateLegalAuthority :
  Braid.legalAuthorityPromoted Braid.canonicalRevolutionaryPracticeBraidSurface ≡ false
braidDoesNotCreateLegalAuthority = refl

braidDoesNotCollapseTraditions :
  Braid.braidCollapsesTraditions Braid.canonicalRevolutionaryPracticeBraidSurface ≡ false
braidDoesNotCollapseTraditions = refl

------------------------------------------------------------------------
-- Mabo-specific cross-checks: continuity, recognition, extinguishment remain
-- separate even after relational/intersectional cross-pollination.
------------------------------------------------------------------------

hallContinuityStillOnContinuityAxis :
  Minimal.axis Minimal.hallContinuityReceipt ≡ Minimal.existenceContinuityAxis
hallContinuityStillOnContinuityAxis = refl

hallRecognitionStillOnConditionAxis :
  Minimal.axis Minimal.hallRecognitionConditionReceipt ≡ Minimal.recognitionConditionAxis
hallRecognitionStillOnConditionAxis = refl

hallExtinguishmentStillOnExtinguishmentAxis :
  Minimal.axis Minimal.hallExtinguishmentReceipt ≡ Minimal.extinguishmentAxis
hallExtinguishmentStillOnExtinguishmentAxis = refl

hallRecognitionSourceTextVerified :
  Verify.authoritativeTranscriptionVerified Verify.hallRecognitionNotPrerequisiteVerified ≡ true
hallRecognitionSourceTextVerified = refl

amoduContinuityStillPrimaryTextNative :
  Primary.textQuality Primary.amoduCessionContinuityProposition ≡ Primary.textNativePrimary
amoduContinuityStillPrimaryTextNative = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data RecognitionCreatesAntecedentRight : Set where
data SovereigntyChangeAloneExtinguishesAntecedentRight : Set where
data SovereigntyChangeLeavesEveryLegalRelationUntouched : Set where
data GovernanceRecognitionRuleIsNativeTitleDoctrine : Set where
data SweetgrassReciprocityCreatesLegalHolding : Set where
data RelationalAnalogyErasesSourceAttribution : Set where

aRecognitionDoesNotCreateAntecedentRight : RecognitionCreatesAntecedentRight → ⊥
aRecognitionDoesNotCreateAntecedentRight ()
sovereigntyChangeAloneDoesNotEncodeExtinguishment : SovereigntyChangeAloneExtinguishesAntecedentRight → ⊥
sovereigntyChangeAloneDoesNotEncodeExtinguishment ()
sovereigntyChangeDoesNotMeanEveryRelationIsUntouched : SovereigntyChangeLeavesEveryLegalRelationUntouched → ⊥
sovereigntyChangeDoesNotMeanEveryRelationIsUntouched ()
governanceRecognitionDoesNotBecomeNativeTitleDoctrine : GovernanceRecognitionRuleIsNativeTitleDoctrine → ⊥
governanceRecognitionDoesNotBecomeNativeTitleDoctrine ()
sweetgrassReciprocityDoesNotCreateLegalHolding : SweetgrassReciprocityCreatesLegalHolding → ⊥
sweetgrassReciprocityDoesNotCreateLegalHolding ()
relationalAnalogyDoesNotEraseSourceAttribution : RelationalAnalogyErasesSourceAttribution → ⊥
relationalAnalogyDoesNotEraseSourceAttribution ()
