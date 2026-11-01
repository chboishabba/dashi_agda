module DASHI.Governance.DomainPermeabilityAuthorityTransport where

open import DASHI.Core.Prelude

import DASHI.Governance.AuthorityMandateCore as Authority

------------------------------------------------------------------------
-- Domain permeability / operational-legibility boundary.
--
-- Reusing one representation, ontology, risk score or case-management engine
-- across domains does not transport the authority that justified its use in
-- the source domain.  This is a governance theorem about typed scope, not a
-- claim that any named vendor or deployment is abusive.
------------------------------------------------------------------------

record OperationalMachinery : Set₁ where
  field
    Domain : Set
    Subject : Set
    Representation : Set
    represent : Domain → Subject → Representation

open OperationalMachinery public

record DomainAuthority
  (M : OperationalMachinery) : Set₁ where
  field
    authorised : Domain M → Subject M → Set

open DomainAuthority public

record SharedMachineryUse
  (M : OperationalMachinery) : Set₁ where
  field
    sourceDomain : Domain M
    targetDomain : Domain M
    subject : Subject M
    sameRepresentation :
      represent M sourceDomain subject
      ≡ represent M targetDomain subject

------------------------------------------------------------------------
-- Exact countermodel: identical representation in two domains while authority
-- is inhabited in only one of them.
------------------------------------------------------------------------

data ExampleDomain : Set where
  sourceDomain : ExampleDomain
  targetDomain : ExampleDomain

data ExampleSubject : Set where
  subject : ExampleSubject

data ExampleRepresentation : Set where
  profile : ExampleRepresentation

exampleMachinery : OperationalMachinery
exampleMachinery =
  record
    { Domain = ExampleDomain
    ; Subject = ExampleSubject
    ; Representation = ExampleRepresentation
    ; represent = λ _ _ → profile
    }

exampleAuthority : DomainAuthority exampleMachinery
exampleAuthority =
  record
    { authorised = authority
    }
  where
    authority : ExampleDomain → ExampleSubject → Set
    authority sourceDomain subject = ⊤
    authority targetDomain subject = ⊥

representationsCoincide :
  represent exampleMachinery sourceDomain subject
  ≡ represent exampleMachinery targetDomain subject
representationsCoincide = refl

sourceIsAuthorised :
  DomainAuthority.authorised exampleAuthority sourceDomain subject
sourceIsAuthorised = tt

targetAuthorityImpossible :
  DomainAuthority.authorised exampleAuthority targetDomain subject → ⊥
targetAuthorityImpossible authority = authority

sameMachineryDoesNotTransportAuthority :
  (represent exampleMachinery sourceDomain subject
    ≡ represent exampleMachinery targetDomain subject →
   DomainAuthority.authorised exampleAuthority sourceDomain subject →
   DomainAuthority.authorised exampleAuthority targetDomain subject) →
  ⊥
sameMachineryDoesNotTransportAuthority transport =
  targetAuthorityImpossible
    (transport representationsCoincide sourceIsAuthorised)

------------------------------------------------------------------------
-- Cross-pollination with AuthorityMandateCore: admissible public authority is
-- explicitly scope-bearing, recallable and reviewable there.  This module does
-- not manufacture a mandate merely from a reused technical representation.
------------------------------------------------------------------------

record DomainTransportReceipt : Set where
  constructor domainTransportReceipt
  field
    sameTechnicalGrammarImpliesSameMandate : Bool
    targetDomainNeedsOwnAuthorityWitness : Bool
    representationEqualityCreatesLegalAuthority : Bool
    vendorIdentityCreatesAuthority : Bool
    domainPermeabilityRequiresGovernanceReview : Bool

canonicalDomainTransportReceipt : DomainTransportReceipt
canonicalDomainTransportReceipt =
  domainTransportReceipt false true false false true
