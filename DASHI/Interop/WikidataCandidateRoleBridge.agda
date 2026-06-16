module DASHI.Interop.WikidataCandidateRoleBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
import DASHI.Interop.RoleGrammarCore as RoleCore

------------------------------------------------------------------------
-- Wikidata candidate role bridge.
--
-- This module is a receipt surface only.  Wikidata contributes candidate
-- entities and superclass/relation/domain hints.  It does not assign a DASHI
-- formal role, select a PNF fibre, compute residuals, or commit an ITIR typed
-- term.  DASHI/PNF owns role-in-context plus fibre/residual assignment, and
-- ITIR owns committed receipt authority.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Wikidata candidate identity and hints.

data QID : Set where
  Q7368 :
    QID

  Q283 :
    QID

  externalQID :
    String →
    QID

qidLabel : QID → String
qidLabel Q7368 =
  "Q7368"
qidLabel Q283 =
  "Q283"
qidLabel (externalQID label) =
  label

record CandidateEntity : Set where
  constructor candidateEntity
  field
    candidateQID :
      QID

    candidateSurface :
      String

open CandidateEntity public

data CandidateSuperclassHint : Set where
  superclassHint :
    String →
    CandidateSuperclassHint

data CandidateRelationHint : Set where
  relationHint :
    String →
    CandidateRelationHint

data CandidateDomainHint : Set where
  domainHint :
    String →
    CandidateDomainHint

record CandidateHintBundle : Set where
  constructor candidateHintBundle
  field
    hintedEntity :
      CandidateEntity

    candidateSuperclassHints :
      List CandidateSuperclassHint

    candidateRelationHints :
      List CandidateRelationHint

    candidateDomainHints :
      List CandidateDomainHint

    wikidataHintOnly :
      Bool

    wikidataHintOnlyIsTrue :
      wikidataHintOnly ≡ true

open CandidateHintBundle public

record WikidataCandidateSurface : Set where
  constructor wikidataCandidateSurface
  field
    wikidataEntity :
      CandidateEntity

    wikidataHints :
      CandidateHintBundle

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

open WikidataCandidateSurface public

------------------------------------------------------------------------
-- DASHI/PNF role-in-context assignment vocabulary.
--
-- Candidate fibre/role/residual constructors remain bridge-specific public
-- names, while generic domain, formal-role, bridge-strength, admission, and
-- authority classes are delegated to DASHI.Interop.RoleGrammarCore.

data RoleGrammarFibre : Set where
  biologicalTaxonFibre :
    RoleGrammarFibre

  lexicalSurfaceFibre :
    RoleGrammarFibre

  labourTransportFibre :
    RoleGrammarFibre

  chemicalSubstanceFibre :
    RoleGrammarFibre

  environmentalMediumFibre :
    RoleGrammarFibre

  resourceGovernanceFibre :
    RoleGrammarFibre

  metaphorCarrierFibre :
    RoleGrammarFibre

  externalCandidateFibre :
    String →
    RoleGrammarFibre

CandidateFibre : Set
CandidateFibre =
  RoleGrammarFibre

data RoleGrammarRole : Set where
  speciesCandidateRole :
    RoleGrammarRole

  packAnimalCandidateRole :
    RoleGrammarRole

  lexicalSenseCandidateRole :
    RoleGrammarRole

  chemicalSubstanceCandidateRole :
    RoleGrammarRole

  environmentalMediumCandidateRole :
    RoleGrammarRole

  resourceCommodityCandidateRole :
    RoleGrammarRole

  metaphorCarrierCandidateRole :
    RoleGrammarRole

  externalCandidateRole :
    String →
    RoleGrammarRole

CandidateRole : Set
CandidateRole =
  RoleGrammarRole

data RoleGrammarResidual : Set where
  exactCandidateResidual :
    RoleGrammarResidual

  partialCandidateResidual :
    RoleGrammarResidual

  noTypedMeetCandidateResidual :
    RoleGrammarResidual

  scopeExceededCandidateResidual :
    RoleGrammarResidual

  unresolvedCandidateResidual :
    RoleGrammarResidual

CandidateResidual : Set
CandidateResidual =
  RoleGrammarResidual

data RoleGrammarFormalRole : Set where
  formalRoleInContext :
    RoleGrammarFibre →
    RoleGrammarRole →
    RoleGrammarResidual →
    RoleGrammarFormalRole

FormalRole : Set
FormalRole =
  RoleGrammarFormalRole

candidateFormalRole :
  CandidateFibre →
  CandidateRole →
  CandidateResidual →
  FormalRole
candidateFormalRole fibre role residual =
  formalRoleInContext fibre role residual

candidateFibreDomain :
  CandidateFibre →
  RoleCore.DomainLabel
candidateFibreDomain biologicalTaxonFibre =
  RoleCore.donkeyDomain
candidateFibreDomain lexicalSurfaceFibre =
  RoleCore.genericDomain
candidateFibreDomain labourTransportFibre =
  RoleCore.donkeyDomain
candidateFibreDomain chemicalSubstanceFibre =
  RoleCore.genericDomain
candidateFibreDomain environmentalMediumFibre =
  RoleCore.genericDomain
candidateFibreDomain resourceGovernanceFibre =
  RoleCore.economyDomain
candidateFibreDomain metaphorCarrierFibre =
  RoleCore.genericDomain
candidateFibreDomain (externalCandidateFibre label) =
  RoleCore.namedDomain label

candidateRoleCoreFormalRole :
  CandidateRole →
  RoleCore.FormalRole
candidateRoleCoreFormalRole speciesCandidateRole =
  RoleCore.observableRole
candidateRoleCoreFormalRole packAnimalCandidateRole =
  RoleCore.operatorRole
candidateRoleCoreFormalRole lexicalSenseCandidateRole =
  RoleCore.evidenceRole
candidateRoleCoreFormalRole chemicalSubstanceCandidateRole =
  RoleCore.carrierSpaceRole
candidateRoleCoreFormalRole environmentalMediumCandidateRole =
  RoleCore.carrierSpaceRole
candidateRoleCoreFormalRole resourceCommodityCandidateRole =
  RoleCore.metricRole
candidateRoleCoreFormalRole metaphorCarrierCandidateRole =
  RoleCore.metaphorRole
candidateRoleCoreFormalRole (externalCandidateRole label) =
  RoleCore.namedFormalRole label

candidateResidualBridgeStrength :
  CandidateResidual →
  RoleCore.BridgeStrength
candidateResidualBridgeStrength exactCandidateResidual =
  RoleCore.exactBridge
candidateResidualBridgeStrength partialCandidateResidual =
  RoleCore.partialBridge
candidateResidualBridgeStrength noTypedMeetCandidateResidual =
  RoleCore.noBridge
candidateResidualBridgeStrength scopeExceededCandidateResidual =
  RoleCore.weakBridge
candidateResidualBridgeStrength unresolvedCandidateResidual =
  RoleCore.weakBridge

candidateRoleCoreReceipt :
  CandidateFibre →
  CandidateRole →
  CandidateResidual →
  RoleCore.RoleFamily
candidateRoleCoreReceipt fibre role residual =
  RoleCore.roleFamily
    (candidateFibreDomain fibre)
    (RoleCore.domainLabelText (candidateFibreDomain fibre))
    (candidateRoleCoreFormalRole role ∷ [])
    (candidateRoleCoreFormalRole role)
    (candidateResidualBridgeStrength residual)
    RoleCore.candidateAdmission
    RoleCore.candidateOnlyClass
    false
    refl
    "Wikidata candidate role grammar delegates generic role-family receipt fields to RoleGrammarCore."

data CandidateFormalRoleEntailment : Set where
  noFormalRoleEntailed :
    CandidateFormalRoleEntailment

  formalRoleEntailedByPNF :
    FormalRole →
    CandidateFormalRoleEntailment

record PNFCandidateAssignment : Set where
  constructor pnfCandidateAssignment
  field
    pnfCandidate :
      WikidataCandidateSurface

    pnfFibre :
      CandidateFibre

    pnfRole :
      CandidateRole

    pnfResidual :
      CandidateResidual

    pnfFormalRole :
      FormalRole

    pnfFormalRoleMatches :
      pnfFormalRole ≡ formalRoleInContext pnfFibre pnfRole pnfResidual

open PNFCandidateAssignment public

pnfAssignmentFromGrammar :
  WikidataCandidateSurface →
  CandidateFibre →
  CandidateRole →
  CandidateResidual →
  PNFCandidateAssignment
pnfAssignmentFromGrammar candidate fibre role residual =
  pnfCandidateAssignment
    candidate
    fibre
    role
    residual
    (candidateFormalRole fibre role residual)
    refl

------------------------------------------------------------------------
-- Commit status and authority.

data RoleGrammarCommitStatus : Set where
  wikidataCandidateOnly :
    RoleGrammarCommitStatus

  pnfRoleAssigned :
    RoleGrammarCommitStatus

  itirCommittedWithReceipt :
    RoleGrammarCommitStatus

  rejectedCandidate :
    RoleGrammarCommitStatus

TypedTermCommitStatus : Set
TypedTermCommitStatus =
  RoleGrammarCommitStatus

data RoleGrammarAuthority : Set where
  noTypedTermAuthority :
    RoleGrammarAuthority

  pnfLocalTypingAuthority :
    RoleGrammarAuthority

  itirCommittedReceiptAuthority :
    RoleGrammarAuthority
TypedTermAuthority : Set
TypedTermAuthority =
  RoleGrammarAuthority

statusCoreTypedStatus :
  TypedTermCommitStatus →
  RoleCore.TypedStatus
statusCoreTypedStatus wikidataCandidateOnly =
  RoleCore.candidateStatus
statusCoreTypedStatus pnfRoleAssigned =
  RoleCore.committedStatus
statusCoreTypedStatus itirCommittedWithReceipt =
  RoleCore.committedStatus
statusCoreTypedStatus rejectedCandidate =
  RoleCore.candidateStatus

statusCoreAdmission :
  RoleGrammarCommitStatus →
  RoleCore.AdmissionStatus
statusCoreAdmission wikidataCandidateOnly =
  RoleCore.candidateAdmission
statusCoreAdmission pnfRoleAssigned =
  RoleCore.committedAdmission
statusCoreAdmission itirCommittedWithReceipt =
  RoleCore.committedAdmission
statusCoreAdmission rejectedCandidate =
  RoleCore.rejectedAdmission

statusCoreAuthorityClass :
  RoleGrammarCommitStatus →
  RoleCore.AuthorityClass
statusCoreAuthorityClass wikidataCandidateOnly =
  RoleCore.noAuthorityClass
statusCoreAuthorityClass pnfRoleAssigned =
  RoleCore.localCommitClass
statusCoreAuthorityClass itirCommittedWithReceipt =
  RoleCore.bridgeReceiptClass
statusCoreAuthorityClass rejectedCandidate =
  RoleCore.noAuthorityClass

authorityFromCoreClass :
  RoleCore.AuthorityClass →
  RoleGrammarAuthority
authorityFromCoreClass RoleCore.noAuthorityClass =
  noTypedTermAuthority
authorityFromCoreClass RoleCore.candidateOnlyClass =
  noTypedTermAuthority
authorityFromCoreClass RoleCore.localCommitClass =
  pnfLocalTypingAuthority
authorityFromCoreClass RoleCore.bridgeReceiptClass =
  itirCommittedReceiptAuthority
authorityFromCoreClass RoleCore.externalAuthorityRequiredClass =
  noTypedTermAuthority

statusAuthority : TypedTermCommitStatus → TypedTermAuthority
statusAuthority status =
  authorityFromCoreClass (statusCoreAuthorityClass status)

record TypedTerm : Set where
  constructor typedTerm
  field
    typedEntity :
      CandidateEntity

    typedSurface :
      String

    typedFibre :
      CandidateFibre

    typedRole :
      CandidateRole

    typedResidual :
      CandidateResidual

    typedFormalRole :
      FormalRole

    typedStatus :
      TypedTermCommitStatus

    typedReceiptId :
      String

    typedAuthority :
      TypedTermAuthority

    typedAuthorityMatches :
      typedAuthority ≡ statusAuthority typedStatus

open TypedTerm public

typedTermCoreReceipt :
  TypedTerm →
  RoleCore.GenericTypedTerm CandidateEntity
typedTermCoreReceipt term =
  RoleCore.genericTypedTerm
    zero
    (typedEntity term)
    (typedSurface term)
    (qidLabel (candidateQID (typedEntity term)))
    (candidateFibreDomain (typedFibre term))
    (candidateRoleCoreFormalRole (typedRole term))
    (statusCoreTypedStatus (typedStatus term))
    (statusCoreAuthorityClass (typedStatus term))
    (candidateResidualBridgeStrength (typedResidual term))
    (statusCoreAdmission (typedStatus term))
    (typedReceiptId term)
    "Candidate bridge typed term projected into RoleGrammarCore; no external authority is created."

typedTermCoreReceiptHasNoExternalAuthority :
  (term : TypedTerm) →
  RoleCore.typedTermExternalAuthority (typedTermCoreReceipt term) ≡ false
typedTermCoreReceiptHasNoExternalAuthority term with typedStatus term
... | wikidataCandidateOnly =
  refl
... | pnfRoleAssigned =
  refl
... | itirCommittedWithReceipt =
  refl
... | rejectedCandidate =
  refl

record ITIRTypedTermCommit : Set where
  constructor itirTypedTermCommit
  field
    committedAssignment :
      PNFCandidateAssignment

    commitStatus :
      TypedTermCommitStatus

    commitStatusIsITIRReceipt :
      commitStatus ≡ itirCommittedWithReceipt

    commitReceiptId :
      String

    committedTerm :
      TypedTerm

    committedTermStatusMatches :
      typedStatus committedTerm ≡ commitStatus

    committedTermAuthorityMatches :
      typedAuthority committedTerm ≡ itirCommittedReceiptAuthority

open ITIRTypedTermCommit public

typedTermFromPNF :
  PNFCandidateAssignment →
  String →
  TypedTerm
typedTermFromPNF assignment receipt =
  typedTerm
    (wikidataEntity (pnfCandidate assignment))
    (candidateSurface (wikidataEntity (pnfCandidate assignment)))
    (pnfFibre assignment)
    (pnfRole assignment)
    (pnfResidual assignment)
    (pnfFormalRole assignment)
    pnfRoleAssigned
    receipt
    pnfLocalTypingAuthority
    refl

typedTermFromITIR :
  PNFCandidateAssignment →
  String →
  TypedTerm
typedTermFromITIR assignment receipt =
  typedTerm
    (wikidataEntity (pnfCandidate assignment))
    (candidateSurface (wikidataEntity (pnfCandidate assignment)))
    (pnfFibre assignment)
    (pnfRole assignment)
    (pnfResidual assignment)
    (pnfFormalRole assignment)
    itirCommittedWithReceipt
    receipt
    itirCommittedReceiptAuthority
    refl

uncommittedCandidateAuthority :
  WikidataCandidateSurface →
  TypedTermAuthority
uncommittedCandidateAuthority candidate =
  noTypedTermAuthority

candidateIdentityFormalRoleAuthority :
  CandidateEntity →
  TypedTermAuthority
candidateIdentityFormalRoleAuthority entity =
  noTypedTermAuthority

candidateIdentityFormalRoleEntailment :
  CandidateEntity →
  CandidateFormalRoleEntailment
candidateIdentityFormalRoleEntailment entity =
  noFormalRoleEntailed

------------------------------------------------------------------------
-- Donkey Q7368 examples with multiple roles.

donkeyEntity : CandidateEntity
donkeyEntity =
  candidateEntity Q7368 "donkey"

donkeyHints : CandidateHintBundle
donkeyHints =
  candidateHintBundle
    donkeyEntity
    (superclassHint "domesticated equine"
      ∷ superclassHint "mammal"
      ∷ [])
    (relationHint "subclass candidate"
      ∷ relationHint "used by humans candidate"
      ∷ [])
    (domainHint "biology"
      ∷ domainHint "agriculture"
      ∷ domainHint "lexical surface"
      ∷ [])
    true
    refl

donkeyCandidate : WikidataCandidateSurface
donkeyCandidate =
  wikidataCandidateSurface
    donkeyEntity
    donkeyHints
    true
    refl

donkeySpeciesAssignment : PNFCandidateAssignment
donkeySpeciesAssignment =
  pnfAssignmentFromGrammar
    donkeyCandidate
    biologicalTaxonFibre
    speciesCandidateRole
    exactCandidateResidual

donkeyPackAnimalAssignment : PNFCandidateAssignment
donkeyPackAnimalAssignment =
  pnfAssignmentFromGrammar
    donkeyCandidate
    labourTransportFibre
    packAnimalCandidateRole
    partialCandidateResidual

donkeyLexicalAssignment : PNFCandidateAssignment
donkeyLexicalAssignment =
  pnfAssignmentFromGrammar
    donkeyCandidate
    lexicalSurfaceFibre
    lexicalSenseCandidateRole
    exactCandidateResidual

donkeySpeciesTypedTerm : TypedTerm
donkeySpeciesTypedTerm =
  typedTermFromITIR donkeySpeciesAssignment "itir:receipt:donkey:species:Q7368"

donkeyPackAnimalTypedTerm : TypedTerm
donkeyPackAnimalTypedTerm =
  typedTermFromITIR donkeyPackAnimalAssignment "itir:receipt:donkey:pack-animal:Q7368"

donkeyLexicalTypedTerm : TypedTerm
donkeyLexicalTypedTerm =
  typedTermFromITIR donkeyLexicalAssignment "itir:receipt:donkey:lexical:Q7368"

donkeyPackAnimalCommit : ITIRTypedTermCommit
donkeyPackAnimalCommit =
  itirTypedTermCommit
    donkeyPackAnimalAssignment
    itirCommittedWithReceipt
    refl
    "itir:receipt:donkey:pack-animal:Q7368"
    donkeyPackAnimalTypedTerm
    refl
    refl

------------------------------------------------------------------------
-- Water Q283 examples with multiple roles.

waterEntity : CandidateEntity
waterEntity =
  candidateEntity Q283 "water"

waterHints : CandidateHintBundle
waterHints =
  candidateHintBundle
    waterEntity
    (superclassHint "chemical compound"
      ∷ superclassHint "transparent liquid candidate"
      ∷ [])
    (relationHint "has part hydrogen candidate"
      ∷ relationHint "has part oxygen candidate"
      ∷ relationHint "environmental medium candidate"
      ∷ [])
    (domainHint "chemistry"
      ∷ domainHint "hydrology"
      ∷ domainHint "resource governance"
      ∷ domainHint "metaphor"
      ∷ [])
    true
    refl

waterCandidate : WikidataCandidateSurface
waterCandidate =
  wikidataCandidateSurface
    waterEntity
    waterHints
    true
    refl

waterChemicalAssignment : PNFCandidateAssignment
waterChemicalAssignment =
  pnfAssignmentFromGrammar
    waterCandidate
    chemicalSubstanceFibre
    chemicalSubstanceCandidateRole
    exactCandidateResidual

waterMediumAssignment : PNFCandidateAssignment
waterMediumAssignment =
  pnfAssignmentFromGrammar
    waterCandidate
    environmentalMediumFibre
    environmentalMediumCandidateRole
    partialCandidateResidual

waterResourceAssignment : PNFCandidateAssignment
waterResourceAssignment =
  pnfAssignmentFromGrammar
    waterCandidate
    resourceGovernanceFibre
    resourceCommodityCandidateRole
    partialCandidateResidual

waterMetaphorAssignment : PNFCandidateAssignment
waterMetaphorAssignment =
  pnfAssignmentFromGrammar
    waterCandidate
    metaphorCarrierFibre
    metaphorCarrierCandidateRole
    scopeExceededCandidateResidual

waterChemicalTypedTerm : TypedTerm
waterChemicalTypedTerm =
  typedTermFromITIR waterChemicalAssignment "itir:receipt:water:chemical:Q283"

waterMediumTypedTerm : TypedTerm
waterMediumTypedTerm =
  typedTermFromITIR waterMediumAssignment "itir:receipt:water:medium:Q283"

waterResourceTypedTerm : TypedTerm
waterResourceTypedTerm =
  typedTermFromITIR waterResourceAssignment "itir:receipt:water:resource:Q283"

waterMetaphorTypedTerm : TypedTerm
waterMetaphorTypedTerm =
  typedTermFromITIR waterMetaphorAssignment "itir:receipt:water:metaphor:Q283"

waterChemicalCommit : ITIRTypedTermCommit
waterChemicalCommit =
  itirTypedTermCommit
    waterChemicalAssignment
    itirCommittedWithReceipt
    refl
    "itir:receipt:water:chemical:Q283"
    waterChemicalTypedTerm
    refl
    refl

------------------------------------------------------------------------
-- Receipt proofs.

qidEntityIdentityDoesNotEntailFormalRole :
  ∀ entity →
  candidateIdentityFormalRoleEntailment entity ≡ noFormalRoleEntailed
qidEntityIdentityDoesNotEntailFormalRole entity =
  refl

donkeyQIDIdentityDoesNotEntailFormalRole :
  candidateIdentityFormalRoleEntailment donkeyEntity ≡ noFormalRoleEntailed
donkeyQIDIdentityDoesNotEntailFormalRole =
  refl

waterQIDIdentityDoesNotEntailFormalRole :
  candidateIdentityFormalRoleEntailment waterEntity ≡ noFormalRoleEntailed
waterQIDIdentityDoesNotEntailFormalRole =
  refl

qidEntityIdentityHasNoTypedTermAuthority :
  ∀ entity →
  candidateIdentityFormalRoleAuthority entity ≡ noTypedTermAuthority
qidEntityIdentityHasNoTypedTermAuthority entity =
  refl

record SameSurfaceEntityDifferentTypedTerms (left right : TypedTerm) : Set where
  constructor sameSurfaceEntityDifferentTypedTerms
  field
    sameTypedEntity :
      typedEntity left ≡ typedEntity right

    sameTypedSurface :
      typedSurface left ≡ typedSurface right

    leftFibreReceipt :
      CandidateFibre

    leftFibreMatches :
      typedFibre left ≡ leftFibreReceipt

    leftRoleReceipt :
      CandidateRole

    leftRoleMatches :
      typedRole left ≡ leftRoleReceipt

    rightFibreReceipt :
      CandidateFibre

    rightFibreMatches :
      typedFibre right ≡ rightFibreReceipt

    rightRoleReceipt :
      CandidateRole

    rightRoleMatches :
      typedRole right ≡ rightRoleReceipt

open SameSurfaceEntityDifferentTypedTerms public

donkeySameSurfaceEntitySpeciesPackAnimalDifferentTypedTerms :
  SameSurfaceEntityDifferentTypedTerms
    donkeySpeciesTypedTerm
    donkeyPackAnimalTypedTerm
donkeySameSurfaceEntitySpeciesPackAnimalDifferentTypedTerms =
  sameSurfaceEntityDifferentTypedTerms
    refl
    refl
    biologicalTaxonFibre
    refl
    speciesCandidateRole
    refl
    labourTransportFibre
    refl
    packAnimalCandidateRole
    refl

waterSameSurfaceEntityChemicalResourceDifferentTypedTerms :
  SameSurfaceEntityDifferentTypedTerms
    waterChemicalTypedTerm
    waterResourceTypedTerm
waterSameSurfaceEntityChemicalResourceDifferentTypedTerms =
  sameSurfaceEntityDifferentTypedTerms
    refl
    refl
    chemicalSubstanceFibre
    refl
    chemicalSubstanceCandidateRole
    refl
    resourceGovernanceFibre
    refl
    resourceCommodityCandidateRole
    refl

uncommittedCandidateHasNoAuthority :
  ∀ candidate →
  uncommittedCandidateAuthority candidate ≡ noTypedTermAuthority
uncommittedCandidateHasNoAuthority candidate =
  refl

donkeyUncommittedCandidateHasNoAuthority :
  uncommittedCandidateAuthority donkeyCandidate ≡ noTypedTermAuthority
donkeyUncommittedCandidateHasNoAuthority =
  refl

waterUncommittedCandidateHasNoAuthority :
  uncommittedCandidateAuthority waterCandidate ≡ noTypedTermAuthority
waterUncommittedCandidateHasNoAuthority =
  refl

wikidataCandidateStatusHasNoAuthority :
  statusAuthority wikidataCandidateOnly ≡ noTypedTermAuthority
wikidataCandidateStatusHasNoAuthority =
  refl

itirReceiptStatusHasCommitAuthority :
  statusAuthority itirCommittedWithReceipt ≡ itirCommittedReceiptAuthority
itirReceiptStatusHasCommitAuthority =
  refl

canonicalCandidateEntities : List CandidateEntity
canonicalCandidateEntities =
  donkeyEntity
  ∷ waterEntity
  ∷ []

canonicalCandidateEntityCount : Nat
canonicalCandidateEntityCount =
  listCount canonicalCandidateEntities

canonicalCandidateEntityCountIsTwo :
  canonicalCandidateEntityCount ≡ suc (suc zero)
canonicalCandidateEntityCountIsTwo =
  refl

canonicalBoundaryNotes : List String
canonicalBoundaryNotes =
  "Wikidata QID/entity identity is candidate identity only"
  ∷ "Superclass, relation, and domain values are hints, not FormalRole evidence"
  ∷ "DASHI/PNF assigns CandidateFibre, CandidateRole, and residual in context"
  ∷ "ITIR commits a TypedTerm only when a receipt is present"
  ∷ "The same surface/entity may produce multiple typed terms across fibres"
  ∷ []
