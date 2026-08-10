module DASHI.Cognition.PNF.ProofRelevantIdentityFibres where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.NumericAuthority
open import DASHI.Cognition.PNF.SparseFibredFrontier

------------------------------------------------------------------------
-- Local surface identity, document/corpus identity and external-world identity
-- are distinct authority strata.  Only an explicit external authority carries
-- permission to assert world-canonical identity.
------------------------------------------------------------------------

data IdentityAuthority : Set where
  surfaceLocal : IdentityAuthority
  documentDerived : IdentityAuthority
  corpusDerived : IdentityAuthority
  externalAuthority : IdentityAuthority

data WorldCanonicalPermission : IdentityAuthority → Set where
  externalAuthorityMayNameWorldEntity :
    WorldCanonicalPermission externalAuthority

surfaceIdentityCannotClaimWorldIdentity :
  WorldCanonicalPermission surfaceLocal → ⊥
surfaceIdentityCannotClaimWorldIdentity ()

documentIdentityCannotClaimWorldIdentity :
  WorldCanonicalPermission documentDerived → ⊥
documentIdentityCannotClaimWorldIdentity ()

corpusIdentityCannotClaimWorldIdentity :
  WorldCanonicalPermission corpusDerived → ⊥
corpusIdentityCannotClaimWorldIdentity ()

------------------------------------------------------------------------
-- Identity evidence is proof-relevant.  Paragraph co-scope, proximity and
-- lexical co-occurrence are represented explicitly as inadmissible evidence,
-- so there is no constructor that can project them into an identity fibre.
------------------------------------------------------------------------

data IdentityEvidenceKind : Set where
  resolutionAnchorEvidence : IdentityEvidenceKind
  appositionEvidence : IdentityEvidenceKind
  properNameExpansionEvidence : IdentityEvidenceKind
  titleRoleClosureEvidence : IdentityEvidenceKind
  anaphorDemandResolutionEvidence : IdentityEvidenceKind
  explicitAliasEvidence : IdentityEvidenceKind
  definitionEquivalenceEvidence : IdentityEvidenceKind
  typedDemandUniqueEvidence : IdentityEvidenceKind
  corpusClosureEvidence : IdentityEvidenceKind
  externalAlignmentEvidence : IdentityEvidenceKind
  paragraphCoScopeEvidence : IdentityEvidenceKind
  lexicalProximityEvidence : IdentityEvidenceKind

data IdentityProjectionPermission : IdentityEvidenceKind → Set where
  resolutionAnchorMayProject :
    IdentityProjectionPermission resolutionAnchorEvidence
  appositionMayProject :
    IdentityProjectionPermission appositionEvidence
  properNameExpansionMayProject :
    IdentityProjectionPermission properNameExpansionEvidence
  titleRoleClosureMayProject :
    IdentityProjectionPermission titleRoleClosureEvidence
  anaphorResolutionMayProject :
    IdentityProjectionPermission anaphorDemandResolutionEvidence
  explicitAliasMayProject :
    IdentityProjectionPermission explicitAliasEvidence
  definitionEquivalenceMayProject :
    IdentityProjectionPermission definitionEquivalenceEvidence
  typedUniqueMayProject :
    IdentityProjectionPermission typedDemandUniqueEvidence
  corpusClosureMayProject :
    IdentityProjectionPermission corpusClosureEvidence
  externalAlignmentMayProject :
    IdentityProjectionPermission externalAlignmentEvidence

paragraphCoScopeCannotProveIdentity :
  IdentityProjectionPermission paragraphCoScopeEvidence → ⊥
paragraphCoScopeCannotProveIdentity ()

lexicalProximityCannotProveIdentity :
  IdentityProjectionPermission lexicalProximityEvidence → ⊥
lexicalProximityCannotProveIdentity ()

------------------------------------------------------------------------
-- Canonical entities are bases over which immutable local objects are fibred.
-- A witness records the source object, target base, evidence kind, authority,
-- and candidate multiplicity.  It does not rewrite the local object.
------------------------------------------------------------------------

record CanonicalEntity : Set where
  constructor canonicalEntity
  field
    canonicalEntityIdentity : Nat
    canonicalAuthority : IdentityAuthority

open CanonicalEntity public

record IdentityWitness : Set where
  constructor identityWitness
  field
    witnessSourceObject : ObjectId
    witnessTargetEntity : CanonicalEntity
    witnessEvidenceKind : IdentityEvidenceKind
    witnessAuthority : IdentityAuthority
    witnessCandidateCount : Nat
    witnessProjectionPermission :
      IdentityProjectionPermission witnessEvidenceKind

open IdentityWitness public

data WitnessAdmission : Set where
  candidateWitness acceptedWitness rejectedWitness supersededWitness :
    WitnessAdmission

record AdmittedIdentityWitness : Set where
  constructor admittedIdentityWitness
  field
    admittedWitness : IdentityWitness
    admission : WitnessAdmission
    admissionIsAccepted : admission ≡ acceptedWitness

open AdmittedIdentityWitness public

------------------------------------------------------------------------
-- Candidate multiplicity remains indexed exactly as in sparse frontier
-- resolution.  Only the unique-witness branch has an identity projection.
------------------------------------------------------------------------

data IdentityProjection : WitnessMultiplicity → Set where
  uniqueIdentityProjection :
    AdmittedIdentityWitness → IdentityProjection oneWitness

noWitnessCannotProjectIdentity : IdentityProjection noWitness → ⊥
noWitnessCannotProjectIdentity ()

ambiguousWitnessesCannotProjectIdentity :
  IdentityProjection severalWitnesses → ⊥
ambiguousWitnessesCannotProjectIdentity ()

record IdentityFibreMember : Set where
  constructor identityFibreMember
  field
    fibreLocalObject : ObjectId
    fibreEntity : CanonicalEntity
    fibreWitness : AdmittedIdentityWitness
    fibreProjection : IdentityProjection oneWitness
    fibreSourceMatchesWitness :
      fibreLocalObject ≡ witnessSourceObject (admittedWitness fibreWitness)
    fibreEntityMatchesWitness :
      canonicalEntityIdentity fibreEntity ≡
        canonicalEntityIdentity
          (witnessTargetEntity (admittedWitness fibreWitness))

open IdentityFibreMember public

------------------------------------------------------------------------
-- Runtime correspondence: the source surface may be observed without granting
-- any world-identity authority.  An external alignment is a separate witness
-- carrying a separate permission.
------------------------------------------------------------------------

record IdentityAuthorityBoundary : Set where
  constructor identityAuthorityBoundary
  field
    surfaceHasNoWorldPermission :
      WorldCanonicalPermission surfaceLocal → ⊥
    documentHasNoWorldPermission :
      WorldCanonicalPermission documentDerived → ⊥
    corpusHasNoWorldPermission :
      WorldCanonicalPermission corpusDerived → ⊥
    externalHasWorldPermission :
      WorldCanonicalPermission externalAuthority
    coScopeHasNoIdentityPermission :
      IdentityProjectionPermission paragraphCoScopeEvidence → ⊥
    proximityHasNoIdentityPermission :
      IdentityProjectionPermission lexicalProximityEvidence → ⊥

open IdentityAuthorityBoundary public

canonicalIdentityAuthorityBoundary : IdentityAuthorityBoundary
canonicalIdentityAuthorityBoundary =
  identityAuthorityBoundary
    surfaceIdentityCannotClaimWorldIdentity
    documentIdentityCannotClaimWorldIdentity
    corpusIdentityCannotClaimWorldIdentity
    externalAuthorityMayNameWorldEntity
    paragraphCoScopeCannotProveIdentity
    lexicalProximityCannotProveIdentity
