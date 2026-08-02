module DASHI.Governance.AuthorityMandateCore where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Core.RelationAlgebraCore as Relation
import DASHI.Interop.RoleGrammarCore as RoleGrammar

------------------------------------------------------------------------
-- Reusable public-authority / mandate core.
--
-- Conceptual precedent:
--   Hanna Fenichel Pitkin, The Concept of Representation (1967).
--   Book; no DOI assigned.
--
-- This module formalizes only a relation grammar.  It does not determine who
-- actually represents a real constituency and it cannot self-issue political
-- legitimacy.
------------------------------------------------------------------------

data Never : Set where

data AuthoritySource : Set where
  constituencyMandate : AuthoritySource
  constitutionalDelegation : AuthoritySource
  judicialWarrant : AuthoritySource
  administrativeSubdelegation : AuthoritySource
  possessionOfForce : AuthoritySource
  eliteAgreementAlone : AuthoritySource
  externalRecognitionAlone : AuthoritySource

AdmissibleAuthoritySource : AuthoritySource → Set
AdmissibleAuthoritySource constituencyMandate = ⊤
AdmissibleAuthoritySource constitutionalDelegation = ⊤
AdmissibleAuthoritySource judicialWarrant = ⊤
AdmissibleAuthoritySource administrativeSubdelegation = ⊤
AdmissibleAuthoritySource possessionOfForce = Never
AdmissibleAuthoritySource eliteAgreementAlone = Never
AdmissibleAuthoritySource externalRecognitionAlone = Never

possessionOfForceRejected :
  AdmissibleAuthoritySource possessionOfForce →
  Never
possessionOfForceRejected ()

eliteAgreementAloneRejected :
  AdmissibleAuthoritySource eliteAgreementAlone →
  Never
eliteAgreementAloneRejected ()

externalRecognitionAloneRejected :
  AdmissibleAuthoritySource externalRecognitionAlone →
  Never
externalRecognitionAloneRejected ()

record Mandate : Set₁ where
  field
    Constituency : Set
    Representative : Set
    Scope : Set
    Term : Set

    representedBy :
      Relation.Rel Constituency Representative

    authorisedFor :
      Representative →
      Scope →
      Set

    termOf :
      Representative →
      Term

    recallable :
      Constituency →
      Representative →
      Set

    reviewable :
      Representative →
      Set

open Mandate public

record NonAlienatingMandate
  (mandate : Mandate) : Set₁ where
  field
    mandateRemainsWithConstituency :
      ∀ constituency representative →
      representedBy mandate constituency representative →
      recallable mandate constituency representative

    representedAgentIsReviewable :
      ∀ constituency representative →
      representedBy mandate constituency representative →
      reviewable mandate representative

open NonAlienatingMandate public

MandateDomain :
  (mandate : Mandate) →
  Constituency mandate →
  Set
MandateDomain mandate constituency =
  Relation.Domain (representedBy mandate) constituency

MandateRange :
  (mandate : Mandate) →
  Representative mandate →
  Set
MandateRange mandate representative =
  Relation.Range (representedBy mandate) representative

record ScopedAuthority
  (mandate : Mandate) : Set₁ where
  field
    source : AuthoritySource
    sourceAdmissible : AdmissibleAuthoritySource source
    constituency : Constituency mandate
    representative : Representative mandate
    scope : Scope mandate
    representationWitness :
      representedBy mandate constituency representative
    scopeWitness :
      authorisedFor mandate representative scope
    recallWitness :
      recallable mandate constituency representative
    reviewWitness :
      reviewable mandate representative

open ScopedAuthority public

------------------------------------------------------------------------
-- Role-grammar cross-pollination.
------------------------------------------------------------------------

governanceDomain : RoleGrammar.DomainLabel
governanceDomain =
  RoleGrammar.namedDomain "Governance"

mandateRole : RoleGrammar.FormalRole
mandateRole =
  RoleGrammar.namedFormalRole "MandateRelation"

delegationRole : RoleGrammar.FormalRole
delegationRole =
  RoleGrammar.namedFormalRole "Delegation"

recallRole : RoleGrammar.FormalRole
recallRole =
  RoleGrammar.namedFormalRole "Recall"

authorityBoundaryRole : RoleGrammar.FormalRole
authorityBoundaryRole =
  RoleGrammar.authorityBoundaryRole

governanceRoleFamily : RoleGrammar.RoleFamily
governanceRoleFamily =
  RoleGrammar.roleFamily
    governanceDomain
    "Governance"
    (mandateRole
      ∷ delegationRole
      ∷ recallRole
      ∷ RoleGrammar.residualRole
      ∷ RoleGrammar.evidenceRole
      ∷ authorityBoundaryRole
      ∷ [])
    mandateRole
    RoleGrammar.partialBridge
    RoleGrammar.candidateAdmission
    RoleGrammar.candidateOnlyClass
    false
    refl
    "Governance role assignments are local typed relations only; actual popular, legal and political authority require external recognition and practice."

governanceRoleFamilyHasNoExternalAuthority :
  RoleGrammar.familyExternalAuthority governanceRoleFamily ≡ false
governanceRoleFamilyHasNoExternalAuthority = refl

record MandateAuthorityBoundary : Set where
  constructor mandateAuthorityBoundary
  field
    forceCreatesAuthority : Bool
    eliteAgreementCreatesAuthority : Bool
    externalRecognitionAloneCreatesAuthority : Bool
    delegationAlienatesConstituencySovereignty : Bool
    mandateRequiresScope : Bool
    mandateRequiresRecall : Bool
    mandateRequiresReview : Bool
    formalModelCreatesPopularLegitimacy : Bool

canonicalMandateAuthorityBoundary : MandateAuthorityBoundary
canonicalMandateAuthorityBoundary =
  mandateAuthorityBoundary
    false
    false
    false
    false
    true
    true
    true
    false

canonicalAuthorityMandateCoreReceipt :
  GenericReceipt.GenericReceipt
canonicalAuthorityMandateCoreReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "non-alienating authority mandate core"
    "DASHI.Governance.AuthorityMandateCore"
    "canonicalMandateAuthorityBoundary"
    "types authority as a source-scoped, recallable and reviewable relation rather than an actor-owned substance"
    "actual constituency recognition, legal validity and political legitimacy remain external to the formal carrier"
    "agda -i . DASHI/Governance/AuthorityMandateCore.agda"
