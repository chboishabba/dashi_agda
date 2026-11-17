module DASHI.Interop.RoleGrammarCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Reusable Domain x FormalRole grammar core.
--
-- The core records typed role assignment in an operator-theory style:
-- a domain family supplies admissible formal roles, a role functor chooses
-- the family for a domain, and a typed term commits only local typed-term
-- status.  Candidate and committed terms are deliberately fail-closed with
-- respect to external legal, clinical, cultural, empirical, or scientific
-- authority.

data DomainLabel : Set where
  qiDomain :
    DomainLabel

  donkeyDomain :
    DomainLabel

  lawDomain :
    DomainLabel

  traumaDomain :
    DomainLabel

  urbanDesignDomain :
    DomainLabel

  sweetgrassDomain :
    DomainLabel

  economyDomain :
    DomainLabel

  personBehaviourDomain :
    DomainLabel

  physicsDomain :
    DomainLabel

  genericDomain :
    DomainLabel

  namedDomain :
    String →
    DomainLabel

domainLabelText : DomainLabel → String
domainLabelText qiDomain =
  "Qi"
domainLabelText donkeyDomain =
  "Donkey"
domainLabelText lawDomain =
  "Law"
domainLabelText traumaDomain =
  "Trauma"
domainLabelText urbanDesignDomain =
  "UrbanDesign"
domainLabelText sweetgrassDomain =
  "Sweetgrass"
domainLabelText economyDomain =
  "Economy"
domainLabelText personBehaviourDomain =
  "PersonBehaviour"
domainLabelText physicsDomain =
  "Physics"
domainLabelText genericDomain =
  "Generic"
domainLabelText (namedDomain label) =
  label

canonicalDomainLabels : List DomainLabel
canonicalDomainLabels =
  qiDomain
  ∷ donkeyDomain
  ∷ lawDomain
  ∷ traumaDomain
  ∷ urbanDesignDomain
  ∷ sweetgrassDomain
  ∷ economyDomain
  ∷ personBehaviourDomain
  ∷ physicsDomain
  ∷ genericDomain
  ∷ []

data FormalRole : Set where
  carrierSpaceRole :
    FormalRole

  stateRole :
    FormalRole

  operatorRole :
    FormalRole

  observableRole :
    FormalRole

  spectrumToolRole :
    FormalRole

  boundaryGateRole :
    FormalRole

  obstructionRole :
    FormalRole

  algebraRole :
    FormalRole

  proofObligationRole :
    FormalRole

  decompositionRole :
    FormalRole

  hamiltonianRole :
    FormalRole

  metricRole :
    FormalRole

  projectionRole :
    FormalRole

  residualRole :
    FormalRole

  evidenceRole :
    FormalRole

  metaphorRole :
    FormalRole

  giftRelationRole :
    FormalRole

  typedMeetRole :
    FormalRole

  bridgeReceiptRole :
    FormalRole

  authorityBoundaryRole :
    FormalRole

  namedFormalRole :
    String →
    FormalRole

formalRoleLabel : FormalRole → String
formalRoleLabel carrierSpaceRole =
  "CarrierSpace"
formalRoleLabel stateRole =
  "State"
formalRoleLabel operatorRole =
  "Operator"
formalRoleLabel observableRole =
  "Observable"
formalRoleLabel spectrumToolRole =
  "SpectrumTool"
formalRoleLabel boundaryGateRole =
  "BoundaryGate"
formalRoleLabel obstructionRole =
  "Obstruction"
formalRoleLabel algebraRole =
  "Algebra"
formalRoleLabel proofObligationRole =
  "ProofObligation"
formalRoleLabel decompositionRole =
  "Decomposition"
formalRoleLabel hamiltonianRole =
  "Hamiltonian"
formalRoleLabel metricRole =
  "Metric"
formalRoleLabel projectionRole =
  "Projection"
formalRoleLabel residualRole =
  "Residual"
formalRoleLabel evidenceRole =
  "Evidence"
formalRoleLabel metaphorRole =
  "Metaphor"
formalRoleLabel giftRelationRole =
  "GiftRelation"
formalRoleLabel typedMeetRole =
  "TypedMeet"
formalRoleLabel bridgeReceiptRole =
  "BridgeReceipt"
formalRoleLabel authorityBoundaryRole =
  "AuthorityBoundary"
formalRoleLabel (namedFormalRole label) =
  label

operatorTheoryRoles : List FormalRole
operatorTheoryRoles =
  carrierSpaceRole
  ∷ stateRole
  ∷ operatorRole
  ∷ observableRole
  ∷ spectrumToolRole
  ∷ algebraRole
  ∷ hamiltonianRole
  ∷ metricRole
  ∷ projectionRole
  ∷ []

authorityBoundaryRoles : List FormalRole
authorityBoundaryRoles =
  evidenceRole
  ∷ proofObligationRole
  ∷ bridgeReceiptRole
  ∷ authorityBoundaryRole
  ∷ []

canonicalFormalRoles : List FormalRole
canonicalFormalRoles =
  carrierSpaceRole
  ∷ stateRole
  ∷ operatorRole
  ∷ observableRole
  ∷ spectrumToolRole
  ∷ boundaryGateRole
  ∷ obstructionRole
  ∷ algebraRole
  ∷ proofObligationRole
  ∷ decompositionRole
  ∷ hamiltonianRole
  ∷ metricRole
  ∷ projectionRole
  ∷ residualRole
  ∷ evidenceRole
  ∷ metaphorRole
  ∷ giftRelationRole
  ∷ typedMeetRole
  ∷ bridgeReceiptRole
  ∷ authorityBoundaryRole
  ∷ []

------------------------------------------------------------------------
-- Typed status, authority classes, and bridge admission.

data TypedStatus : Set where
  candidateStatus :
    TypedStatus

  committedStatus :
    TypedStatus

statusLabel : TypedStatus → String
statusLabel candidateStatus =
  "Candidate"
statusLabel committedStatus =
  "Committed"

data AuthorityClass : Set where
  noAuthorityClass :
    AuthorityClass

  candidateOnlyClass :
    AuthorityClass

  localCommitClass :
    AuthorityClass

  bridgeReceiptClass :
    AuthorityClass

  externalAuthorityRequiredClass :
    AuthorityClass

authorityClassLabel : AuthorityClass → String
authorityClassLabel noAuthorityClass =
  "NoAuthority"
authorityClassLabel candidateOnlyClass =
  "CandidateOnly"
authorityClassLabel localCommitClass =
  "LocalCommit"
authorityClassLabel bridgeReceiptClass =
  "BridgeReceipt"
authorityClassLabel externalAuthorityRequiredClass =
  "ExternalAuthorityRequired"

data BridgeStrength : Set where
  noBridge :
    BridgeStrength

  weakBridge :
    BridgeStrength

  partialBridge :
    BridgeStrength

  exactBridge :
    BridgeStrength

bridgeStrengthLabel : BridgeStrength → String
bridgeStrengthLabel noBridge =
  "NoBridge"
bridgeStrengthLabel weakBridge =
  "WeakBridge"
bridgeStrengthLabel partialBridge =
  "PartialBridge"
bridgeStrengthLabel exactBridge =
  "ExactBridge"

data AdmissionStatus : Set where
  candidateAdmission :
    AdmissionStatus

  committedAdmission :
    AdmissionStatus

  blockedPendingBridgeAdmission :
    AdmissionStatus

  rejectedAdmission :
    AdmissionStatus

admissionStatusLabel : AdmissionStatus → String
admissionStatusLabel candidateAdmission =
  "CandidateAdmission"
admissionStatusLabel committedAdmission =
  "CommittedAdmission"
admissionStatusLabel blockedPendingBridgeAdmission =
  "BlockedPendingBridge"
admissionStatusLabel rejectedAdmission =
  "RejectedAdmission"

statusCandidateOnly : TypedStatus → Bool
statusCandidateOnly candidateStatus =
  true
statusCandidateOnly committedStatus =
  false

statusCommitted : TypedStatus → Bool
statusCommitted candidateStatus =
  false
statusCommitted committedStatus =
  true

statusAuthorityClass : TypedStatus → AuthorityClass
statusAuthorityClass candidateStatus =
  candidateOnlyClass
statusAuthorityClass committedStatus =
  localCommitClass

statusLocalCommitAuthority : TypedStatus → Bool
statusLocalCommitAuthority candidateStatus =
  false
statusLocalCommitAuthority committedStatus =
  true

statusCandidateAuthority : TypedStatus → Bool
statusCandidateAuthority candidateStatus =
  false
statusCandidateAuthority committedStatus =
  false

statusExternalAuthority : TypedStatus → Bool
statusExternalAuthority _ =
  false

authorityClassExternalAuthority : AuthorityClass → Bool
authorityClassExternalAuthority noAuthorityClass =
  false
authorityClassExternalAuthority candidateOnlyClass =
  false
authorityClassExternalAuthority localCommitClass =
  false
authorityClassExternalAuthority bridgeReceiptClass =
  false
authorityClassExternalAuthority externalAuthorityRequiredClass =
  false

admissionExternalAuthority : AdmissionStatus → Bool
admissionExternalAuthority _ =
  false

bridgeStrengthExternalAuthority : BridgeStrength → Bool
bridgeStrengthExternalAuthority _ =
  false

candidateStatusHasNoLocalCommitAuthority :
  statusLocalCommitAuthority candidateStatus ≡ false
candidateStatusHasNoLocalCommitAuthority =
  refl

candidateStatusHasNoExternalAuthority :
  statusExternalAuthority candidateStatus ≡ false
candidateStatusHasNoExternalAuthority =
  refl

candidateStatusHasNoCandidateAuthority :
  statusCandidateAuthority candidateStatus ≡ false
candidateStatusHasNoCandidateAuthority =
  refl

committedStatusHasLocalCommitAuthority :
  statusLocalCommitAuthority committedStatus ≡ true
committedStatusHasLocalCommitAuthority =
  refl

committedStatusHasNoCandidateAuthority :
  statusCandidateAuthority committedStatus ≡ false
committedStatusHasNoCandidateAuthority =
  refl

committedStatusHasNoExternalAuthority :
  statusExternalAuthority committedStatus ≡ false
committedStatusHasNoExternalAuthority =
  refl

authorityClassDoesNotCreateExternalAuthority :
  ∀ authorityClass →
  authorityClassExternalAuthority authorityClass ≡ false
authorityClassDoesNotCreateExternalAuthority noAuthorityClass =
  refl
authorityClassDoesNotCreateExternalAuthority candidateOnlyClass =
  refl
authorityClassDoesNotCreateExternalAuthority localCommitClass =
  refl
authorityClassDoesNotCreateExternalAuthority bridgeReceiptClass =
  refl
authorityClassDoesNotCreateExternalAuthority externalAuthorityRequiredClass =
  refl

admissionDoesNotCreateExternalAuthority :
  ∀ admission →
  admissionExternalAuthority admission ≡ false
admissionDoesNotCreateExternalAuthority admission =
  refl

bridgeStrengthDoesNotCreateExternalAuthority :
  ∀ strength →
  bridgeStrengthExternalAuthority strength ≡ false
bridgeStrengthDoesNotCreateExternalAuthority strength =
  refl

------------------------------------------------------------------------
-- Role families and role functors.

record RoleFamily : Set where
  constructor roleFamily
  field
    familyDomain :
      DomainLabel

    familyName :
      String

    familyRoles :
      List FormalRole

    familyDefaultRole :
      FormalRole

    familyBridgeStrength :
      BridgeStrength

    familyAdmissionStatus :
      AdmissionStatus

    familyAuthorityClass :
      AuthorityClass

    familyExternalAuthority :
      Bool

    familyExternalAuthorityIsFalse :
      familyExternalAuthority ≡ false

    familyReceiptNote :
      String

open RoleFamily public

domainCanonicalRoles : DomainLabel → List FormalRole
domainCanonicalRoles qiDomain =
  carrierSpaceRole
  ∷ stateRole
  ∷ operatorRole
  ∷ observableRole
  ∷ metricRole
  ∷ evidenceRole
  ∷ []
domainCanonicalRoles donkeyDomain =
  carrierSpaceRole
  ∷ stateRole
  ∷ operatorRole
  ∷ boundaryGateRole
  ∷ obstructionRole
  ∷ evidenceRole
  ∷ metaphorRole
  ∷ []
domainCanonicalRoles lawDomain =
  stateRole
  ∷ operatorRole
  ∷ boundaryGateRole
  ∷ proofObligationRole
  ∷ evidenceRole
  ∷ projectionRole
  ∷ authorityBoundaryRole
  ∷ []
domainCanonicalRoles traumaDomain =
  stateRole
  ∷ observableRole
  ∷ boundaryGateRole
  ∷ residualRole
  ∷ evidenceRole
  ∷ decompositionRole
  ∷ []
domainCanonicalRoles urbanDesignDomain =
  carrierSpaceRole
  ∷ boundaryGateRole
  ∷ obstructionRole
  ∷ metricRole
  ∷ projectionRole
  ∷ residualRole
  ∷ evidenceRole
  ∷ []
domainCanonicalRoles sweetgrassDomain =
  carrierSpaceRole
  ∷ decompositionRole
  ∷ giftRelationRole
  ∷ metaphorRole
  ∷ evidenceRole
  ∷ []
domainCanonicalRoles economyDomain =
  stateRole
  ∷ operatorRole
  ∷ observableRole
  ∷ metricRole
  ∷ projectionRole
  ∷ residualRole
  ∷ evidenceRole
  ∷ []
domainCanonicalRoles personBehaviourDomain =
  stateRole
  ∷ operatorRole
  ∷ observableRole
  ∷ boundaryGateRole
  ∷ residualRole
  ∷ evidenceRole
  ∷ metaphorRole
  ∷ []
domainCanonicalRoles physicsDomain =
  operatorTheoryRoles
domainCanonicalRoles genericDomain =
  canonicalFormalRoles
domainCanonicalRoles (namedDomain _) =
  canonicalFormalRoles

domainDefaultRole : DomainLabel → FormalRole
domainDefaultRole qiDomain =
  operatorRole
domainDefaultRole donkeyDomain =
  operatorRole
domainDefaultRole lawDomain =
  boundaryGateRole
domainDefaultRole traumaDomain =
  residualRole
domainDefaultRole urbanDesignDomain =
  carrierSpaceRole
domainDefaultRole sweetgrassDomain =
  giftRelationRole
domainDefaultRole economyDomain =
  metricRole
domainDefaultRole personBehaviourDomain =
  observableRole
domainDefaultRole physicsDomain =
  operatorRole
domainDefaultRole genericDomain =
  evidenceRole
domainDefaultRole (namedDomain _) =
  evidenceRole

domainBridgeStrength : DomainLabel → BridgeStrength
domainBridgeStrength qiDomain =
  weakBridge
domainBridgeStrength donkeyDomain =
  weakBridge
domainBridgeStrength lawDomain =
  partialBridge
domainBridgeStrength traumaDomain =
  partialBridge
domainBridgeStrength urbanDesignDomain =
  partialBridge
domainBridgeStrength sweetgrassDomain =
  partialBridge
domainBridgeStrength economyDomain =
  partialBridge
domainBridgeStrength personBehaviourDomain =
  partialBridge
domainBridgeStrength physicsDomain =
  exactBridge
domainBridgeStrength genericDomain =
  noBridge
domainBridgeStrength (namedDomain _) =
  weakBridge

roleFamilyFor : DomainLabel → RoleFamily
roleFamilyFor domain =
  roleFamily
    domain
    (domainLabelText domain)
    (domainCanonicalRoles domain)
    (domainDefaultRole domain)
    (domainBridgeStrength domain)
    candidateAdmission
    candidateOnlyClass
    false
    refl
    "Role-family receipts type assignments only; they do not create external authority."

record RoleFunctor : Set where
  constructor roleFunctor
  field
    familyForDomain :
      DomainLabel → RoleFamily

    roleForDomain :
      DomainLabel → FormalRole

    functorBridgeStrength :
      DomainLabel → BridgeStrength

    functorAdmissionStatus :
      DomainLabel → AdmissionStatus

    candidateAuthority :
      DomainLabel → Bool

    committedAuthority :
      DomainLabel → Bool

    externalAuthority :
      DomainLabel → Bool

    functorExternalAuthorityIsFalse :
      ∀ domain →
      externalAuthority domain ≡ false

open RoleFunctor public

canonicalCandidateAuthority : DomainLabel → Bool
canonicalCandidateAuthority _ =
  false

canonicalCommittedAuthority : DomainLabel → Bool
canonicalCommittedAuthority _ =
  true

canonicalFunctorExternalAuthority : DomainLabel → Bool
canonicalFunctorExternalAuthority _ =
  false

canonicalRoleFunctor : RoleFunctor
canonicalRoleFunctor =
  roleFunctor
    roleFamilyFor
    domainDefaultRole
    domainBridgeStrength
    (λ _ → candidateAdmission)
    canonicalCandidateAuthority
    canonicalCommittedAuthority
    canonicalFunctorExternalAuthority
    (λ _ → refl)

roleFunctorHasNoExternalAuthority :
  ∀ functor domain →
  externalAuthority functor domain ≡ false
roleFunctorHasNoExternalAuthority functor domain =
  functorExternalAuthorityIsFalse functor domain

canonicalRoleFunctorHasNoExternalAuthority :
  ∀ domain →
  externalAuthority canonicalRoleFunctor domain ≡ false
canonicalRoleFunctorHasNoExternalAuthority domain =
  refl

canonicalQiFamilyDomain :
  familyDomain (familyForDomain canonicalRoleFunctor qiDomain) ≡ qiDomain
canonicalQiFamilyDomain =
  refl

canonicalLawDefaultRole :
  roleForDomain canonicalRoleFunctor lawDomain ≡ boundaryGateRole
canonicalLawDefaultRole =
  refl

canonicalGenericRolesAreAllRoles :
  familyRoles (familyForDomain canonicalRoleFunctor genericDomain)
  ≡
  canonicalFormalRoles
canonicalGenericRolesAreAllRoles =
  refl

------------------------------------------------------------------------
-- Generic typed terms and assignment receipts.

record SurfaceEntity : Set where
  constructor surfaceEntity
  field
    surfaceText :
      String

    entityKey :
      String

open SurfaceEntity public

record GenericTypedTerm (Payload : Set) : Set where
  constructor genericTypedTerm
  field
    termId :
      Nat

    payload :
      Payload

    surface :
      String

    entity :
      String

    termDomain :
      DomainLabel

    termRole :
      FormalRole

    termStatus :
      TypedStatus

    termAuthorityClass :
      AuthorityClass

    termBridgeStrength :
      BridgeStrength

    termAdmissionStatus :
      AdmissionStatus

    termReceipt :
      String

    termNote :
      String

open GenericTypedTerm public

typedTermSurfaceEntity :
  ∀ {Payload} →
  GenericTypedTerm Payload →
  SurfaceEntity
typedTermSurfaceEntity term =
  surfaceEntity (surface term) (entity term)

typedTermFamily :
  ∀ {Payload} →
  GenericTypedTerm Payload →
  RoleFamily
typedTermFamily term =
  roleFamilyFor (termDomain term)

typedTermCandidateAuthority :
  ∀ {Payload} →
  GenericTypedTerm Payload →
  Bool
typedTermCandidateAuthority term =
  statusCandidateAuthority (termStatus term)

typedTermLocalCommitAuthority :
  ∀ {Payload} →
  GenericTypedTerm Payload →
  Bool
typedTermLocalCommitAuthority term =
  statusLocalCommitAuthority (termStatus term)

typedTermExternalAuthority :
  ∀ {Payload} →
  GenericTypedTerm Payload →
  Bool
typedTermExternalAuthority term =
  statusExternalAuthority (termStatus term)

typedTermAuthorityClassExternalAuthority :
  ∀ {Payload} →
  GenericTypedTerm Payload →
  Bool
typedTermAuthorityClassExternalAuthority term =
  authorityClassExternalAuthority (termAuthorityClass term)

typedTermAdmissionExternalAuthority :
  ∀ {Payload} →
  GenericTypedTerm Payload →
  Bool
typedTermAdmissionExternalAuthority term =
  admissionExternalAuthority (termAdmissionStatus term)

typedTermBridgeExternalAuthority :
  ∀ {Payload} →
  GenericTypedTerm Payload →
  Bool
typedTermBridgeExternalAuthority term =
  bridgeStrengthExternalAuthority (termBridgeStrength term)

typedTermHasNoExternalAuthority :
  ∀ {Payload} →
  (term : GenericTypedTerm Payload) →
  typedTermExternalAuthority term ≡ false
typedTermHasNoExternalAuthority term with termStatus term
... | candidateStatus =
  refl
... | committedStatus =
  refl

typedTermAuthorityClassHasNoExternalAuthority :
  ∀ {Payload} →
  (term : GenericTypedTerm Payload) →
  typedTermAuthorityClassExternalAuthority term ≡ false
typedTermAuthorityClassHasNoExternalAuthority term =
  authorityClassDoesNotCreateExternalAuthority (termAuthorityClass term)

typedTermAdmissionHasNoExternalAuthority :
  ∀ {Payload} →
  (term : GenericTypedTerm Payload) →
  typedTermAdmissionExternalAuthority term ≡ false
typedTermAdmissionHasNoExternalAuthority term =
  admissionDoesNotCreateExternalAuthority (termAdmissionStatus term)

typedTermBridgeHasNoExternalAuthority :
  ∀ {Payload} →
  (term : GenericTypedTerm Payload) →
  typedTermBridgeExternalAuthority term ≡ false
typedTermBridgeHasNoExternalAuthority term =
  bridgeStrengthDoesNotCreateExternalAuthority (termBridgeStrength term)

surfaceEntityIdentityEntailsRole :
  SurfaceEntity →
  FormalRole →
  Bool
surfaceEntityIdentityEntailsRole _ _ =
  false

surfaceEntityIdentityDoesNotEntailRole :
  ∀ surface formalRole →
  surfaceEntityIdentityEntailsRole surface formalRole ≡ false
surfaceEntityIdentityDoesNotEntailRole surface formalRole =
  refl

roleEntailedBySurfaceEntityIdentity :
  ∀ {Payload} →
  GenericTypedTerm Payload →
  GenericTypedTerm Payload →
  Bool
roleEntailedBySurfaceEntityIdentity _ _ =
  false

typedTermSurfaceEntityIdentityDoesNotEntailRole :
  ∀ {Payload} →
  (left right : GenericTypedTerm Payload) →
  roleEntailedBySurfaceEntityIdentity left right ≡ false
typedTermSurfaceEntityIdentityDoesNotEntailRole left right =
  refl

record RoleAssignmentReceipt (Payload : Set) : Set where
  constructor roleAssignmentReceipt
  field
    assignedTerm :
      GenericTypedTerm Payload

    assignmentFamily :
      RoleFamily

    assignedRole :
      FormalRole

    assignedRoleMatchesTerm :
      assignedRole ≡ termRole assignedTerm

    assignmentStatus :
      TypedStatus

    assignmentStatusMatchesTerm :
      assignmentStatus ≡ termStatus assignedTerm

    assignmentAuthorityClass :
      AuthorityClass

    assignmentAuthorityClassMatchesTerm :
      assignmentAuthorityClass ≡ termAuthorityClass assignedTerm

    assignmentBridgeStrength :
      BridgeStrength

    assignmentBridgeStrengthMatchesTerm :
      assignmentBridgeStrength ≡ termBridgeStrength assignedTerm

    assignmentAdmissionStatus :
      AdmissionStatus

    assignmentAdmissionStatusMatchesTerm :
      assignmentAdmissionStatus ≡ termAdmissionStatus assignedTerm

    candidateAuthorityFlag :
      Bool

    candidateAuthorityMatchesStatus :
      candidateAuthorityFlag ≡ statusCandidateAuthority assignmentStatus

    localCommitAuthorityFlag :
      Bool

    localCommitAuthorityMatchesStatus :
      localCommitAuthorityFlag ≡ statusLocalCommitAuthority assignmentStatus

    externalAuthorityFlag :
      Bool

    receiptExternalAuthorityIsFalse :
      externalAuthorityFlag ≡ false

open RoleAssignmentReceipt public

assignmentCandidateAuthority :
  ∀ {Payload} →
  RoleAssignmentReceipt Payload →
  Bool
assignmentCandidateAuthority receipt =
  candidateAuthorityFlag receipt

assignmentLocalCommitAuthority :
  ∀ {Payload} →
  RoleAssignmentReceipt Payload →
  Bool
assignmentLocalCommitAuthority receipt =
  localCommitAuthorityFlag receipt

assignmentExternalAuthority :
  ∀ {Payload} →
  RoleAssignmentReceipt Payload →
  Bool
assignmentExternalAuthority receipt =
  externalAuthorityFlag receipt

assignmentHasNoExternalAuthority :
  ∀ {Payload} →
  (receipt : RoleAssignmentReceipt Payload) →
  assignmentExternalAuthority receipt ≡ false
assignmentHasNoExternalAuthority receipt =
  receiptExternalAuthorityIsFalse receipt

candidateAssignmentHasNoLocalCommitAuthority :
  ∀ {Payload} →
  (receipt : RoleAssignmentReceipt Payload) →
  assignmentStatus receipt ≡ candidateStatus →
  assignmentLocalCommitAuthority receipt ≡ false
candidateAssignmentHasNoLocalCommitAuthority receipt refl =
  localCommitAuthorityMatchesStatus receipt

candidateAssignmentHasNoExternalAuthority :
  ∀ {Payload} →
  (receipt : RoleAssignmentReceipt Payload) →
  assignmentStatus receipt ≡ candidateStatus →
  assignmentExternalAuthority receipt ≡ false
candidateAssignmentHasNoExternalAuthority receipt statusIsCandidate =
  receiptExternalAuthorityIsFalse receipt

committedAssignmentHasLocalCommitAuthority :
  ∀ {Payload} →
  (receipt : RoleAssignmentReceipt Payload) →
  assignmentStatus receipt ≡ committedStatus →
  assignmentLocalCommitAuthority receipt ≡ true
committedAssignmentHasLocalCommitAuthority receipt refl =
  localCommitAuthorityMatchesStatus receipt

committedAssignmentHasNoExternalAuthority :
  ∀ {Payload} →
  (receipt : RoleAssignmentReceipt Payload) →
  assignmentStatus receipt ≡ committedStatus →
  assignmentExternalAuthority receipt ≡ false
committedAssignmentHasNoExternalAuthority receipt statusIsCommitted =
  receiptExternalAuthorityIsFalse receipt

------------------------------------------------------------------------
-- Canonical lightweight role lists and example terms.

DASHITypedTerm : Set
DASHITypedTerm =
  GenericTypedTerm String

mkCandidateTerm :
  Nat →
  String →
  String →
  DomainLabel →
  FormalRole →
  String →
  DASHITypedTerm
mkCandidateTerm termId surface entity domain role receipt =
  genericTypedTerm
    termId
    receipt
    surface
    entity
    domain
    role
    candidateStatus
    candidateOnlyClass
    (domainBridgeStrength domain)
    candidateAdmission
    receipt
    "Candidate typed-term receipt; no external authority is created."

mkCommittedTerm :
  Nat →
  String →
  String →
  DomainLabel →
  FormalRole →
  String →
  DASHITypedTerm
mkCommittedTerm termId surface entity domain role receipt =
  genericTypedTerm
    termId
    receipt
    surface
    entity
    domain
    role
    committedStatus
    localCommitClass
    (domainBridgeStrength domain)
    committedAdmission
    receipt
    "Committed local typed-term receipt; no external authority is created."

qiOperatorCandidate : DASHITypedTerm
qiOperatorCandidate =
  mkCandidateTerm
    zero
    "qi"
    "entity:qi"
    qiDomain
    operatorRole
    "role-core:qi/operator/candidate"

lawBoundaryGateCommitted : DASHITypedTerm
lawBoundaryGateCommitted =
  mkCommittedTerm
    (suc zero)
    "law"
    "entity:law"
    lawDomain
    boundaryGateRole
    "role-core:law/boundary-gate/committed"

waterCarrierCommitted : DASHITypedTerm
waterCarrierCommitted =
  mkCommittedTerm
    (suc (suc zero))
    "water"
    "entity:water"
    genericDomain
    carrierSpaceRole
    "role-core:water/carrier/committed"

waterObservableCandidate : DASHITypedTerm
waterObservableCandidate =
  mkCandidateTerm
    (suc (suc (suc zero)))
    "water"
    "entity:water"
    genericDomain
    observableRole
    "role-core:water/observable/candidate"

canonicalTypedTerms : List DASHITypedTerm
canonicalTypedTerms =
  qiOperatorCandidate
  ∷ lawBoundaryGateCommitted
  ∷ waterCarrierCommitted
  ∷ waterObservableCandidate
  ∷ []

canonicalWaterRoleTerms : List DASHITypedTerm
canonicalWaterRoleTerms =
  waterCarrierCommitted
  ∷ waterObservableCandidate
  ∷ []

qiOperatorCandidateReceipt : RoleAssignmentReceipt String
qiOperatorCandidateReceipt =
  roleAssignmentReceipt
    qiOperatorCandidate
    (roleFamilyFor qiDomain)
    operatorRole
    refl
    candidateStatus
    refl
    candidateOnlyClass
    refl
    weakBridge
    refl
    candidateAdmission
    refl
    false
    refl
    false
    refl
    false
    refl

lawBoundaryGateCommittedReceipt : RoleAssignmentReceipt String
lawBoundaryGateCommittedReceipt =
  roleAssignmentReceipt
    lawBoundaryGateCommitted
    (roleFamilyFor lawDomain)
    boundaryGateRole
    refl
    committedStatus
    refl
    localCommitClass
    refl
    partialBridge
    refl
    committedAdmission
    refl
    false
    refl
    true
    refl
    false
    refl

waterCarrierCommittedReceipt : RoleAssignmentReceipt String
waterCarrierCommittedReceipt =
  roleAssignmentReceipt
    waterCarrierCommitted
    (roleFamilyFor genericDomain)
    carrierSpaceRole
    refl
    committedStatus
    refl
    localCommitClass
    refl
    noBridge
    refl
    committedAdmission
    refl
    false
    refl
    true
    refl
    false
    refl

waterObservableCandidateReceipt : RoleAssignmentReceipt String
waterObservableCandidateReceipt =
  roleAssignmentReceipt
    waterObservableCandidate
    (roleFamilyFor genericDomain)
    observableRole
    refl
    candidateStatus
    refl
    candidateOnlyClass
    refl
    noBridge
    refl
    candidateAdmission
    refl
    false
    refl
    false
    refl
    false
    refl

canonicalRoleAssignmentReceipts : List (RoleAssignmentReceipt String)
canonicalRoleAssignmentReceipts =
  qiOperatorCandidateReceipt
  ∷ lawBoundaryGateCommittedReceipt
  ∷ waterCarrierCommittedReceipt
  ∷ waterObservableCandidateReceipt
  ∷ []

canonicalAuthorityClasses : List AuthorityClass
canonicalAuthorityClasses =
  noAuthorityClass
  ∷ candidateOnlyClass
  ∷ localCommitClass
  ∷ bridgeReceiptClass
  ∷ externalAuthorityRequiredClass
  ∷ []

canonicalBridgeStrengths : List BridgeStrength
canonicalBridgeStrengths =
  noBridge
  ∷ weakBridge
  ∷ partialBridge
  ∷ exactBridge
  ∷ []

canonicalAdmissionStatuses : List AdmissionStatus
canonicalAdmissionStatuses =
  candidateAdmission
  ∷ committedAdmission
  ∷ blockedPendingBridgeAdmission
  ∷ rejectedAdmission
  ∷ []

canonicalRoleFamilies : List RoleFamily
canonicalRoleFamilies =
  roleFamilyFor qiDomain
  ∷ roleFamilyFor donkeyDomain
  ∷ roleFamilyFor lawDomain
  ∷ roleFamilyFor traumaDomain
  ∷ roleFamilyFor urbanDesignDomain
  ∷ roleFamilyFor sweetgrassDomain
  ∷ roleFamilyFor economyDomain
  ∷ roleFamilyFor personBehaviourDomain
  ∷ roleFamilyFor physicsDomain
  ∷ roleFamilyFor genericDomain
  ∷ []

qiOperatorCandidateHasNoLocalCommitAuthority :
  typedTermLocalCommitAuthority qiOperatorCandidate ≡ false
qiOperatorCandidateHasNoLocalCommitAuthority =
  refl

qiOperatorCandidateHasNoExternalAuthority :
  typedTermExternalAuthority qiOperatorCandidate ≡ false
qiOperatorCandidateHasNoExternalAuthority =
  refl

lawBoundaryGateCommittedHasLocalCommitAuthority :
  typedTermLocalCommitAuthority lawBoundaryGateCommitted ≡ true
lawBoundaryGateCommittedHasLocalCommitAuthority =
  refl

lawBoundaryGateCommittedHasNoExternalAuthority :
  typedTermExternalAuthority lawBoundaryGateCommitted ≡ false
lawBoundaryGateCommittedHasNoExternalAuthority =
  refl

waterSameSurfaceEntityDoesNotEntailObservable :
  roleEntailedBySurfaceEntityIdentity
    waterCarrierCommitted
    waterObservableCandidate
  ≡
  false
waterSameSurfaceEntityDoesNotEntailObservable =
  refl

qiReceiptNoExternalAuthority :
  assignmentExternalAuthority qiOperatorCandidateReceipt ≡ false
qiReceiptNoExternalAuthority =
  refl

lawReceiptNoExternalAuthority :
  assignmentExternalAuthority lawBoundaryGateCommittedReceipt ≡ false
lawReceiptNoExternalAuthority =
  refl

waterCarrierReceiptNoExternalAuthority :
  assignmentExternalAuthority waterCarrierCommittedReceipt ≡ false
waterCarrierReceiptNoExternalAuthority =
  refl

waterObservableReceiptNoExternalAuthority :
  assignmentExternalAuthority waterObservableCandidateReceipt ≡ false
waterObservableReceiptNoExternalAuthority =
  refl

record RoleGrammarCoreReceipt : Set where
  constructor roleGrammarCoreReceipt
  field
    receiptDomains :
      List DomainLabel

    receiptFormalRoles :
      List FormalRole

    receiptAuthorityClasses :
      List AuthorityClass

    receiptBridgeStrengths :
      List BridgeStrength

    receiptAdmissionStatuses :
      List AdmissionStatus

    receiptRoleFunctor :
      RoleFunctor

    receiptRoleFamilies :
      List RoleFamily

    receiptTypedTerms :
      List DASHITypedTerm

    receiptAssignmentReceipts :
      List (RoleAssignmentReceipt String)

    receiptFunctorNoExternalAuthority :
      ∀ domain →
      externalAuthority receiptRoleFunctor domain ≡ false

    receiptCandidateNoLocalCommitAuthority :
      statusLocalCommitAuthority candidateStatus ≡ false

    receiptCandidateNoExternalAuthority :
      statusExternalAuthority candidateStatus ≡ false

    receiptCommittedLocalOnly :
      statusLocalCommitAuthority committedStatus ≡ true

    receiptCommittedNoExternalAuthority :
      statusExternalAuthority committedStatus ≡ false

    receiptSameSurfaceEntityDoesNotEntailRole :
      roleEntailedBySurfaceEntityIdentity
        waterCarrierCommitted
        waterObservableCandidate
      ≡
      false

    receiptPromotesExternalAuthority :
      Bool

    receiptPromotesExternalAuthorityIsFalse :
      receiptPromotesExternalAuthority ≡ false

    receiptNote :
      String

open RoleGrammarCoreReceipt public

canonicalRoleGrammarCoreReceipt :
  RoleGrammarCoreReceipt
canonicalRoleGrammarCoreReceipt =
  roleGrammarCoreReceipt
    canonicalDomainLabels
    canonicalFormalRoles
    canonicalAuthorityClasses
    canonicalBridgeStrengths
    canonicalAdmissionStatuses
    canonicalRoleFunctor
    canonicalRoleFamilies
    canonicalTypedTerms
    canonicalRoleAssignmentReceipts
    canonicalRoleFunctorHasNoExternalAuthority
    candidateStatusHasNoLocalCommitAuthority
    candidateStatusHasNoExternalAuthority
    committedStatusHasLocalCommitAuthority
    committedStatusHasNoExternalAuthority
    waterSameSurfaceEntityDoesNotEntailObservable
    false
    refl
    "Reusable DomainLabel x FormalRole grammar core; checked role assignment receipts do not create external authority."

roleGrammarCoreGenericReceipt :
  RoleGrammarCoreReceipt →
  GenericReceipt.GenericReceipt
roleGrammarCoreGenericReceipt receipt =
  GenericReceipt.mkNonPromotingReceipt
    "role grammar core"
    "DASHI.Interop.RoleGrammarCore"
    "canonicalRoleGrammarCoreReceipt"
    (receiptNote receipt)
    "role grammar receipts remain local typing and bridge metadata; they do not create external authority"
    "agda -i . DASHI/Interop/RoleGrammarCore.agda"

canonicalRoleGrammarCoreGenericReceipt :
  GenericReceipt.GenericReceipt
canonicalRoleGrammarCoreGenericReceipt =
  roleGrammarCoreGenericReceipt canonicalRoleGrammarCoreReceipt
