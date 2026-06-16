module DASHI.Interop.TypedTermRoleFunctor where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
import DASHI.Interop.RoleGrammarCore as Core

------------------------------------------------------------------------
-- Domain x FormalRole typed-term receipt surface.
--
-- This module is a checked object model for role assignment over PNF / DASHI
-- terms.  Reusable role/domain/status/functor vocabulary lives in
-- RoleGrammarCore; this file preserves the typed-term receipt surface and
-- canonical examples while delegating generic grammar and authority predicates.

Domain : Set
Domain =
  Core.DomainLabel

Qi : Domain
Qi =
  Core.qiDomain

Donkey : Domain
Donkey =
  Core.donkeyDomain

Law : Domain
Law =
  Core.lawDomain

Trauma : Domain
Trauma =
  Core.traumaDomain

UrbanDesign : Domain
UrbanDesign =
  Core.urbanDesignDomain

Sweetgrass : Domain
Sweetgrass =
  Core.sweetgrassDomain

Economy : Domain
Economy =
  Core.economyDomain

PersonBehaviour : Domain
PersonBehaviour =
  Core.personBehaviourDomain

generic : Domain
generic =
  Core.genericDomain

domainLabel : Domain → String
domainLabel =
  Core.domainLabelText

canonicalDomains : List Domain
canonicalDomains =
  Core.canonicalDomainLabels

FormalRole : Set
FormalRole =
  Core.FormalRole

CarrierSpace : FormalRole
CarrierSpace =
  Core.carrierSpaceRole

State : FormalRole
State =
  Core.stateRole

Operator : FormalRole
Operator =
  Core.operatorRole

Observable : FormalRole
Observable =
  Core.observableRole

SpectrumTool : FormalRole
SpectrumTool =
  Core.spectrumToolRole

BoundaryGate : FormalRole
BoundaryGate =
  Core.boundaryGateRole

Obstruction : FormalRole
Obstruction =
  Core.obstructionRole

Algebra : FormalRole
Algebra =
  Core.algebraRole

ProofObligation : FormalRole
ProofObligation =
  Core.proofObligationRole

Decomposition : FormalRole
Decomposition =
  Core.decompositionRole

Hamiltonian : FormalRole
Hamiltonian =
  Core.hamiltonianRole

Metric : FormalRole
Metric =
  Core.metricRole

Projection : FormalRole
Projection =
  Core.projectionRole

Residual : FormalRole
Residual =
  Core.residualRole

Evidence : FormalRole
Evidence =
  Core.evidenceRole

Metaphor : FormalRole
Metaphor =
  Core.metaphorRole

GiftRelation : FormalRole
GiftRelation =
  Core.giftRelationRole

formalRoleLabel : FormalRole → String
formalRoleLabel =
  Core.formalRoleLabel

canonicalFormalRoles : List FormalRole
canonicalFormalRoles =
  Core.canonicalFormalRoles

TypedTermStatus : Set
TypedTermStatus =
  Core.TypedStatus

Candidate : TypedTermStatus
Candidate =
  Core.candidateStatus

Committed : TypedTermStatus
Committed =
  Core.committedStatus

statusLabel : TypedTermStatus → String
statusLabel =
  Core.statusLabel

statusCandidateOnly : TypedTermStatus → Bool
statusCandidateOnly =
  Core.statusCandidateOnly

statusLocalCommitAuthority : TypedTermStatus → Bool
statusLocalCommitAuthority =
  Core.statusLocalCommitAuthority

statusExternalAuthority : TypedTermStatus → Bool
statusExternalAuthority =
  Core.statusExternalAuthority

candidateOnlyAssignmentsCarryNoLocalAuthority :
  statusLocalCommitAuthority Candidate ≡ false
candidateOnlyAssignmentsCarryNoLocalAuthority =
  Core.candidateStatusHasNoLocalCommitAuthority

candidateOnlyAssignmentsCarryNoExternalAuthority :
  statusExternalAuthority Candidate ≡ false
candidateOnlyAssignmentsCarryNoExternalAuthority =
  Core.candidateStatusHasNoExternalAuthority

committedStatusIsLocalCommitOnly :
  statusLocalCommitAuthority Committed ≡ true
committedStatusIsLocalCommitOnly =
  Core.committedStatusHasLocalCommitAuthority

committedStatusDoesNotCreateExternalAuthority :
  statusExternalAuthority Committed ≡ false
committedStatusDoesNotCreateExternalAuthority =
  Core.committedStatusHasNoExternalAuthority

RoleFamily : Set
RoleFamily =
  Core.RoleFamily

roleFamily :
  Domain →
  String →
  List FormalRole →
  FormalRole →
  String →
  RoleFamily
roleFamily domain familyName generatedRoles defaultRole familyReceiptNote =
  Core.roleFamily
    domain
    familyName
    generatedRoles
    defaultRole
    (Core.domainBridgeStrength domain)
    Core.candidateAdmission
    Core.candidateOnlyClass
    false
    refl
    familyReceiptNote

familyDomain : RoleFamily → Domain
familyDomain =
  Core.familyDomain

familyName : RoleFamily → String
familyName =
  Core.familyName

generatedRoles : RoleFamily → List FormalRole
generatedRoles =
  Core.familyRoles

defaultRole : RoleFamily → FormalRole
defaultRole =
  Core.familyDefaultRole

familyReceiptNote : RoleFamily → String
familyReceiptNote =
  Core.familyReceiptNote

domainRoles : Domain → List FormalRole
domainRoles =
  Core.domainCanonicalRoles

domainDefaultRole : Domain → FormalRole
domainDefaultRole =
  Core.domainDefaultRole

roleFamilyFor : Domain → RoleFamily
roleFamilyFor =
  Core.roleFamilyFor

noSurfaceEntityRoleAuthority : Domain → Bool
noSurfaceEntityRoleAuthority =
  Core.canonicalFunctorExternalAuthority

noCandidateRoleAuthority : Domain → Bool
noCandidateRoleAuthority =
  Core.canonicalCandidateAuthority

RoleFunctor : Set
RoleFunctor =
  Core.RoleFunctor

familyForDomain : RoleFunctor → Domain → RoleFamily
familyForDomain =
  Core.familyForDomain

surfaceEntityRoleAuthority : RoleFunctor → Domain → Bool
surfaceEntityRoleAuthority =
  Core.externalAuthority

candidateRoleAuthority : RoleFunctor → Domain → Bool
candidateRoleAuthority =
  Core.candidateAuthority

canonicalRoleFunctor : RoleFunctor
canonicalRoleFunctor =
  Core.canonicalRoleFunctor

roleFunctorGeneratesQiFamily :
  familyDomain (familyForDomain canonicalRoleFunctor Qi) ≡ Qi
roleFunctorGeneratesQiFamily =
  Core.canonicalQiFamilyDomain

roleFunctorGeneratesLawFamily :
  defaultRole (familyForDomain canonicalRoleFunctor Law) ≡ BoundaryGate
roleFunctorGeneratesLawFamily =
  refl

roleFunctorSurfaceEntityIdentityHasNoAuthority :
  ∀ domain →
  surfaceEntityRoleAuthority canonicalRoleFunctor domain ≡ false
roleFunctorSurfaceEntityIdentityHasNoAuthority domain =
  Core.canonicalRoleFunctorHasNoExternalAuthority domain

roleFunctorCandidateOnlyHasNoAuthority :
  ∀ domain →
  candidateRoleAuthority canonicalRoleFunctor domain ≡ false
roleFunctorCandidateOnlyHasNoAuthority domain =
  refl

typedTermRoleFunctorCore : RoleFunctor
typedTermRoleFunctorCore =
  Core.canonicalRoleFunctor

typedTermRoleFunctorCoreIsCanonical :
  typedTermRoleFunctorCore ≡ canonicalRoleFunctor
typedTermRoleFunctorCoreIsCanonical =
  refl

------------------------------------------------------------------------
-- Typed terms and assignment receipts.

record SurfaceEntity : Set where
  constructor surfaceEntity
  field
    surfaceText :
      String

    entityIdentity :
      String

open SurfaceEntity public

record TypedTerm : Set where
  constructor typedTerm
  field
    termId :
      Nat

    surface :
      String

    entity :
      String

    domain :
      Domain

    role :
      FormalRole

    status :
      TypedTermStatus

    pnfReceipt :
      String

    termReceiptNote :
      String

open TypedTerm public

typedTermAuthorityClass : TypedTerm → Core.AuthorityClass
typedTermAuthorityClass term =
  Core.statusAuthorityClass (status term)

typedTermBridgeStrength : TypedTerm → Core.BridgeStrength
typedTermBridgeStrength term =
  Core.domainBridgeStrength (domain term)

typedTermAdmissionStatus : TypedTerm → Core.AdmissionStatus
typedTermAdmissionStatus _ =
  Core.candidateAdmission

typedTermToCore : TypedTerm → Core.GenericTypedTerm String
typedTermToCore term =
  Core.genericTypedTerm
    (termId term)
    (pnfReceipt term)
    (surface term)
    (entity term)
    (domain term)
    (role term)
    (status term)
    (typedTermAuthorityClass term)
    (typedTermBridgeStrength term)
    (typedTermAdmissionStatus term)
    (pnfReceipt term)
    (termReceiptNote term)

surfaceEntityToCore : SurfaceEntity → Core.SurfaceEntity
surfaceEntityToCore surfaceEntityValue =
  Core.surfaceEntity
    (surfaceText surfaceEntityValue)
    (entityIdentity surfaceEntityValue)

typedTermSurfaceEntity : TypedTerm → SurfaceEntity
typedTermSurfaceEntity term =
  surfaceEntity (surface term) (entity term)

typedTermFamily : TypedTerm → RoleFamily
typedTermFamily term =
  Core.typedTermFamily (typedTermToCore term)

typedTermCandidateOnly : TypedTerm → Bool
typedTermCandidateOnly term =
  Core.statusCandidateOnly (status term)

typedTermLocalCommitAuthority : TypedTerm → Bool
typedTermLocalCommitAuthority term =
  Core.typedTermLocalCommitAuthority (typedTermToCore term)

typedTermExternalAuthority : TypedTerm → Bool
typedTermExternalAuthority term =
  Core.typedTermExternalAuthority (typedTermToCore term)

roleEntailedBySurfaceEntityIdentity :
  TypedTerm →
  TypedTerm →
  Bool
roleEntailedBySurfaceEntityIdentity left right =
  Core.roleEntailedBySurfaceEntityIdentity
    (typedTermToCore left)
    (typedTermToCore right)

surfaceEntityIdentityEntailsRole :
  SurfaceEntity →
  FormalRole →
  Bool
surfaceEntityIdentityEntailsRole surfaceEntityValue formalRole =
  Core.surfaceEntityIdentityEntailsRole
    (surfaceEntityToCore surfaceEntityValue)
    formalRole

surfaceEntityIdentityDoesNotEntailRole :
  ∀ se formalRole →
  surfaceEntityIdentityEntailsRole se formalRole ≡ false
surfaceEntityIdentityDoesNotEntailRole se formalRole =
  refl

typedTermSurfaceEntityIdentityDoesNotEntailRole :
  ∀ left right →
  roleEntailedBySurfaceEntityIdentity left right ≡ false
typedTermSurfaceEntityIdentityDoesNotEntailRole left right =
  refl

record RoleAssignmentReceipt : Set where
  constructor roleAssignmentReceipt
  field
    assignedTerm :
      TypedTerm

    assignmentFamily :
      RoleFamily

    assignedRole :
      FormalRole

    assignedRoleMatchesTerm :
      assignedRole ≡ role assignedTerm

    assignmentStatus :
      TypedTermStatus

    assignmentStatusMatchesTerm :
      assignmentStatus ≡ status assignedTerm

    candidateOnly :
      Bool

    candidateOnlyMatchesStatus :
      candidateOnly ≡ statusCandidateOnly assignmentStatus

    localCommitAuthority :
      Bool

    localCommitAuthorityMatchesStatus :
      localCommitAuthority ≡ statusLocalCommitAuthority assignmentStatus

    externalAuthority :
      Bool

    externalAuthorityIsFalse :
      externalAuthority ≡ false

open RoleAssignmentReceipt public

statusNeverExternalAuthority :
  ∀ assignmentStatus →
  Core.statusExternalAuthority assignmentStatus ≡ false
statusNeverExternalAuthority Core.candidateStatus =
  refl
statusNeverExternalAuthority Core.committedStatus =
  refl

roleAssignmentFor : TypedTerm → RoleAssignmentReceipt
roleAssignmentFor term =
  roleAssignmentReceipt
    term
    (Core.roleFamilyFor (domain term))
    (role term)
    refl
    (status term)
    refl
    (Core.statusCandidateOnly (status term))
    refl
    (Core.statusLocalCommitAuthority (status term))
    refl
    (Core.statusExternalAuthority (status term))
    (statusNeverExternalAuthority (status term))

assignmentCarriesExternalAuthority :
  RoleAssignmentReceipt →
  Bool
assignmentCarriesExternalAuthority receipt =
  externalAuthority receipt

assignmentCarriesLocalCommitAuthority :
  RoleAssignmentReceipt →
  Bool
assignmentCarriesLocalCommitAuthority receipt =
  localCommitAuthority receipt

candidateReceiptHasNoExternalAuthority :
  ∀ receipt →
  assignmentStatus receipt ≡ Candidate →
  assignmentCarriesExternalAuthority receipt ≡ false
candidateReceiptHasNoExternalAuthority receipt statusIsCandidate =
  externalAuthorityIsFalse receipt

------------------------------------------------------------------------
-- Canonical typed-term examples requested by the receipt.

QiOperator : TypedTerm
QiOperator =
  typedTerm
    zero
    "qi"
    "entity:qi"
    Qi
    Operator
    Candidate
    "pnf:qi/operator"
    "QiOperator records qi as an operator candidate in the Qi role family."

DonkeyOperator : TypedTerm
DonkeyOperator =
  typedTerm
    (suc zero)
    "donkey"
    "entity:donkey"
    Donkey
    Operator
    Candidate
    "pnf:donkey/operator"
    "DonkeyOperator records donkey as an operator candidate in the Donkey role family."

LawBoundaryGate : TypedTerm
LawBoundaryGate =
  typedTerm
    (suc (suc zero))
    "law"
    "entity:law"
    Law
    BoundaryGate
    Committed
    "pnf:law/boundary-gate"
    "LawBoundaryGate is a committed local typed term, not legal authority."

TraumaResidual : TypedTerm
TraumaResidual =
  typedTerm
    (suc (suc (suc zero)))
    "trauma"
    "entity:trauma"
    Trauma
    Residual
    Candidate
    "pnf:trauma/residual"
    "TraumaResidual records a clinical-language residual candidate without clinical authority."

waterCarrierSpace : TypedTerm
waterCarrierSpace =
  typedTerm
    (suc (suc (suc (suc zero))))
    "water"
    "entity:water"
    generic
    CarrierSpace
    Committed
    "pnf:water/carrier-space"
    "Water may be a carrier space in a generic typed role receipt."

waterObservable : TypedTerm
waterObservable =
  typedTerm
    (suc (suc (suc (suc (suc zero)))))
    "water"
    "entity:water"
    generic
    Observable
    Candidate
    "pnf:water/observable"
    "The same water surface/entity can be observed under Observable role."

waterBoundaryGate : TypedTerm
waterBoundaryGate =
  typedTerm
    (suc (suc (suc (suc (suc (suc zero))))))
    "water"
    "entity:water"
    UrbanDesign
    BoundaryGate
    Candidate
    "pnf:water/boundary-gate"
    "Urban-design water can be proposed as a boundary gate without authority."

waterGiftRelation : TypedTerm
waterGiftRelation =
  typedTerm
    (suc (suc (suc (suc (suc (suc (suc zero)))))))
    "water"
    "entity:water"
    Sweetgrass
    GiftRelation
    Candidate
    "pnf:water/gift-relation"
    "Sweetgrass water can be proposed as a gift relation without cultural authority."

canonicalTypedTerms : List TypedTerm
canonicalTypedTerms =
  QiOperator
  ∷ DonkeyOperator
  ∷ LawBoundaryGate
  ∷ TraumaResidual
  ∷ waterCarrierSpace
  ∷ waterObservable
  ∷ waterBoundaryGate
  ∷ waterGiftRelation
  ∷ []

waterMultipleRoles : List TypedTerm
waterMultipleRoles =
  waterCarrierSpace
  ∷ waterObservable
  ∷ waterBoundaryGate
  ∷ waterGiftRelation
  ∷ []

QiOperatorReceipt : RoleAssignmentReceipt
QiOperatorReceipt =
  roleAssignmentFor QiOperator

DonkeyOperatorReceipt : RoleAssignmentReceipt
DonkeyOperatorReceipt =
  roleAssignmentFor DonkeyOperator

LawBoundaryGateReceipt : RoleAssignmentReceipt
LawBoundaryGateReceipt =
  roleAssignmentFor LawBoundaryGate

TraumaResidualReceipt : RoleAssignmentReceipt
TraumaResidualReceipt =
  roleAssignmentFor TraumaResidual

waterCarrierSpaceReceipt : RoleAssignmentReceipt
waterCarrierSpaceReceipt =
  roleAssignmentFor waterCarrierSpace

waterObservableReceipt : RoleAssignmentReceipt
waterObservableReceipt =
  roleAssignmentFor waterObservable

waterBoundaryGateReceipt : RoleAssignmentReceipt
waterBoundaryGateReceipt =
  roleAssignmentFor waterBoundaryGate

waterGiftRelationReceipt : RoleAssignmentReceipt
waterGiftRelationReceipt =
  roleAssignmentFor waterGiftRelation

canonicalRoleAssignmentReceipts : List RoleAssignmentReceipt
canonicalRoleAssignmentReceipts =
  QiOperatorReceipt
  ∷ DonkeyOperatorReceipt
  ∷ LawBoundaryGateReceipt
  ∷ TraumaResidualReceipt
  ∷ waterCarrierSpaceReceipt
  ∷ waterObservableReceipt
  ∷ waterBoundaryGateReceipt
  ∷ waterGiftRelationReceipt
  ∷ []

------------------------------------------------------------------------
-- Concrete refl receipts.

QiOperatorRoleIsOperator :
  role QiOperator ≡ Operator
QiOperatorRoleIsOperator =
  refl

DonkeyOperatorRoleIsOperator :
  role DonkeyOperator ≡ Operator
DonkeyOperatorRoleIsOperator =
  refl

LawBoundaryGateRoleIsBoundaryGate :
  role LawBoundaryGate ≡ BoundaryGate
LawBoundaryGateRoleIsBoundaryGate =
  refl

TraumaResidualRoleIsResidual :
  role TraumaResidual ≡ Residual
TraumaResidualRoleIsResidual =
  refl

LawBoundaryGateIsCommitted :
  status LawBoundaryGate ≡ Committed
LawBoundaryGateIsCommitted =
  refl

QiOperatorCandidateOnlyCarriesNoLocalAuthority :
  typedTermLocalCommitAuthority QiOperator ≡ false
QiOperatorCandidateOnlyCarriesNoLocalAuthority =
  refl

DonkeyOperatorCandidateOnlyCarriesNoLocalAuthority :
  typedTermLocalCommitAuthority DonkeyOperator ≡ false
DonkeyOperatorCandidateOnlyCarriesNoLocalAuthority =
  refl

TraumaResidualCandidateOnlyCarriesNoLocalAuthority :
  typedTermLocalCommitAuthority TraumaResidual ≡ false
TraumaResidualCandidateOnlyCarriesNoLocalAuthority =
  refl

waterObservableCandidateOnlyCarriesNoLocalAuthority :
  typedTermLocalCommitAuthority waterObservable ≡ false
waterObservableCandidateOnlyCarriesNoLocalAuthority =
  refl

waterBoundaryGateCandidateOnlyCarriesNoLocalAuthority :
  typedTermLocalCommitAuthority waterBoundaryGate ≡ false
waterBoundaryGateCandidateOnlyCarriesNoLocalAuthority =
  refl

waterGiftRelationCandidateOnlyCarriesNoLocalAuthority :
  typedTermLocalCommitAuthority waterGiftRelation ≡ false
waterGiftRelationCandidateOnlyCarriesNoLocalAuthority =
  refl

QiOperatorCandidateOnlyCarriesNoExternalAuthority :
  typedTermExternalAuthority QiOperator ≡ false
QiOperatorCandidateOnlyCarriesNoExternalAuthority =
  refl

LawBoundaryGateCommittedCarriesNoExternalAuthority :
  typedTermExternalAuthority LawBoundaryGate ≡ false
LawBoundaryGateCommittedCarriesNoExternalAuthority =
  refl

waterSurfaceSameForCarrierAndObservable :
  surface waterCarrierSpace ≡ surface waterObservable
waterSurfaceSameForCarrierAndObservable =
  refl

waterEntitySameForCarrierAndObservable :
  entity waterCarrierSpace ≡ entity waterObservable
waterEntitySameForCarrierAndObservable =
  refl

waterSurfaceEntityDoesNotEntailCarrierSpace :
  surfaceEntityIdentityEntailsRole
    (typedTermSurfaceEntity waterCarrierSpace)
    CarrierSpace
  ≡
  false
waterSurfaceEntityDoesNotEntailCarrierSpace =
  refl

waterSurfaceEntityDoesNotEntailObservable :
  surfaceEntityIdentityEntailsRole
    (typedTermSurfaceEntity waterObservable)
    Observable
  ≡
  false
waterSurfaceEntityDoesNotEntailObservable =
  refl

waterSameSurfaceEntityDoesNotEntailRolePair :
  roleEntailedBySurfaceEntityIdentity
    waterCarrierSpace
    waterObservable
  ≡
  false
waterSameSurfaceEntityDoesNotEntailRolePair =
  refl

waterSameSurfaceEntityDoesNotEntailUrbanBoundaryGate :
  roleEntailedBySurfaceEntityIdentity
    waterCarrierSpace
    waterBoundaryGate
  ≡
  false
waterSameSurfaceEntityDoesNotEntailUrbanBoundaryGate =
  refl

waterSameSurfaceEntityDoesNotEntailSweetgrassGiftRelation :
  roleEntailedBySurfaceEntityIdentity
    waterCarrierSpace
    waterGiftRelation
  ≡
  false
waterSameSurfaceEntityDoesNotEntailSweetgrassGiftRelation =
  refl

candidateOnlyQiReceiptNoExternalAuthority :
  assignmentCarriesExternalAuthority QiOperatorReceipt ≡ false
candidateOnlyQiReceiptNoExternalAuthority =
  refl

candidateOnlyDonkeyReceiptNoExternalAuthority :
  assignmentCarriesExternalAuthority DonkeyOperatorReceipt ≡ false
candidateOnlyDonkeyReceiptNoExternalAuthority =
  refl

candidateOnlyTraumaReceiptNoExternalAuthority :
  assignmentCarriesExternalAuthority TraumaResidualReceipt ≡ false
candidateOnlyTraumaReceiptNoExternalAuthority =
  refl

candidateOnlyWaterObservableReceiptNoExternalAuthority :
  assignmentCarriesExternalAuthority waterObservableReceipt ≡ false
candidateOnlyWaterObservableReceiptNoExternalAuthority =
  refl

candidateOnlyWaterBoundaryGateReceiptNoExternalAuthority :
  assignmentCarriesExternalAuthority waterBoundaryGateReceipt ≡ false
candidateOnlyWaterBoundaryGateReceiptNoExternalAuthority =
  refl

candidateOnlyWaterGiftRelationReceiptNoExternalAuthority :
  assignmentCarriesExternalAuthority waterGiftRelationReceipt ≡ false
candidateOnlyWaterGiftRelationReceiptNoExternalAuthority =
  refl

committedWaterCarrierReceiptNoExternalAuthority :
  assignmentCarriesExternalAuthority waterCarrierSpaceReceipt ≡ false
committedWaterCarrierReceiptNoExternalAuthority =
  refl

committedLawBoundaryGateReceiptNoExternalAuthority :
  assignmentCarriesExternalAuthority LawBoundaryGateReceipt ≡ false
committedLawBoundaryGateReceiptNoExternalAuthority =
  refl

genericRoleFamilyContainsAllFormalRoles :
  generatedRoles (roleFamilyFor generic) ≡ canonicalFormalRoles
genericRoleFamilyContainsAllFormalRoles =
  refl

sweetgrassRoleFamilyDefaultsToGiftRelation :
  defaultRole (roleFamilyFor Sweetgrass) ≡ GiftRelation
sweetgrassRoleFamilyDefaultsToGiftRelation =
  refl

urbanDesignRoleFamilyDefaultsToCarrierSpace :
  defaultRole (roleFamilyFor UrbanDesign) ≡ CarrierSpace
urbanDesignRoleFamilyDefaultsToCarrierSpace =
  refl

personBehaviourRoleFamilyDefaultsToObservable :
  defaultRole (roleFamilyFor PersonBehaviour) ≡ Observable
personBehaviourRoleFamilyDefaultsToObservable =
  refl

------------------------------------------------------------------------
-- Compact receipt rollup.

record TypedTermRoleFunctorReceipt : Set where
  constructor typedTermRoleFunctorReceipt
  field
    receiptDomains :
      List Domain

    receiptDomainsAreCanonical :
      receiptDomains ≡ canonicalDomains

    receiptRoles :
      List FormalRole

    receiptRolesAreCanonical :
      receiptRoles ≡ canonicalFormalRoles

    receiptFunctor :
      RoleFunctor

    receiptFunctorIsCanonical :
      receiptFunctor ≡ canonicalRoleFunctor

    receiptTypedTerms :
      List TypedTerm

    receiptTypedTermsAreCanonical :
      receiptTypedTerms ≡ canonicalTypedTerms

    receiptAssignments :
      List RoleAssignmentReceipt

    receiptAssignmentsAreCanonical :
      receiptAssignments ≡ canonicalRoleAssignmentReceipts

    receiptSurfaceEntityIdentityAuthority :
      Bool

    receiptSurfaceEntityIdentityAuthorityIsFalse :
      receiptSurfaceEntityIdentityAuthority ≡ false

    receiptCandidateOnlyAuthority :
      Bool

    receiptCandidateOnlyAuthorityIsFalse :
      receiptCandidateOnlyAuthority ≡ false

    receiptExternalAuthority :
      Bool

    receiptExternalAuthorityIsFalse :
      receiptExternalAuthority ≡ false

open TypedTermRoleFunctorReceipt public

canonicalTypedTermRoleFunctorReceipt :
  TypedTermRoleFunctorReceipt
canonicalTypedTermRoleFunctorReceipt =
  typedTermRoleFunctorReceipt
    canonicalDomains
    refl
    canonicalFormalRoles
    refl
    canonicalRoleFunctor
    refl
    canonicalTypedTerms
    refl
    canonicalRoleAssignmentReceipts
    refl
    false
    refl
    false
    refl
    false
    refl

receiptCandidateOnlyAssignmentsHaveNoAuthority :
  receiptCandidateOnlyAuthority canonicalTypedTermRoleFunctorReceipt ≡ false
receiptCandidateOnlyAssignmentsHaveNoAuthority =
  refl

receiptSurfaceEntityIdentityDoesNotEntailRole :
  receiptSurfaceEntityIdentityAuthority
    canonicalTypedTermRoleFunctorReceipt
  ≡
  false
receiptSurfaceEntityIdentityDoesNotEntailRole =
  refl

canonicalReceiptExternalAuthorityIsFalse :
  receiptExternalAuthority canonicalTypedTermRoleFunctorReceipt ≡ false
canonicalReceiptExternalAuthorityIsFalse =
  refl
