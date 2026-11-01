module DASHI.Governance.RepresentationCarrierVerificationCore where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Representation / carrier / authority / verification core.
--
-- A subject may have to act on a representation because independent
-- verification of the underlying carrier is expensive, unavailable, or
-- outside their competence.  A discrepancy is therefore formalized before
-- any claim about deception, fraudulent state of mind, abuse or legal wrong.
------------------------------------------------------------------------

record RepresentationCarrierSystem : Set₁ where
  field
    Carrier : Set
    Representation : Set
    Evidence : Set
    Authority : Set
    Subject : Set

    present : Authority → Carrier → Representation
    verify : Carrier → Evidence
    agrees : Representation → Evidence → Set
    reliesOn : Subject → Authority → Representation → Set
    independentVerificationAvailable : Subject → Carrier → Set

open RepresentationCarrierSystem public

record RepresentationDiscrepancy
  (S : RepresentationCarrierSystem) : Set₁ where
  field
    authority : Authority S
    carrier : Carrier S
    representation : Representation S
    evidence : Evidence S
    representationWasPresented : present S authority carrier ≡ representation
    evidenceWasIndependentlyProduced : verify S carrier ≡ evidence
    disagreement : agrees S representation evidence → ⊥

record Misrepresentation
  (S : RepresentationCarrierSystem) : Set₁ where
  field
    discrepancy : RepresentationDiscrepancy S

record DeceptionCandidate
  (S : RepresentationCarrierSystem) : Set₁ where
  field
    misrepresentation : Misrepresentation S
    KnowledgeOrRecklessness : Set
    knowledgeOrRecklessness : KnowledgeOrRecklessness
    DeceptiveIntent : Set
    deceptiveIntent : DeceptiveIntent

record FraudCandidate
  (S : RepresentationCarrierSystem) : Set₁ where
  field
    deceptionCandidate : DeceptionCandidate S
    JurisdictionSpecificElements : Set
    jurisdictionSpecificElements : JurisdictionSpecificElements

------------------------------------------------------------------------
-- Promotion boundaries.
------------------------------------------------------------------------

data DiscrepancyEstablishesDeception : Set where

data DeceptionCandidateEstablishesLegalFraud : Set where

data OriginEvidenceEstablishesLabourPractice : Set where

discrepancyDoesNotEstablishDeception :
  DiscrepancyEstablishesDeception → ⊥
discrepancyDoesNotEstablishDeception ()

deceptionCandidateDoesNotEstablishLegalFraud :
  DeceptionCandidateEstablishesLegalFraud → ⊥
deceptionCandidateDoesNotEstablishLegalFraud ()

originEvidenceDoesNotEstablishLabourPractice :
  OriginEvidenceEstablishesLabourPractice → ⊥
originEvidenceDoesNotEstablishLabourPractice ()

record RepresentationCarrierBoundary : Set where
  constructor representationCarrierBoundary
  field
    representationEqualsCarrier : Bool
    discrepancyEqualsDeception : Bool
    deceptionCandidateEqualsLegalFraud : Bool
    oneEvidenceDomainPromotesAnotherDomain : Bool
    independentVerificationMattersUnderDependency : Bool
    provenanceMustBePreservedAcrossPromotion : Bool

canonicalRepresentationCarrierBoundary : RepresentationCarrierBoundary
canonicalRepresentationCarrierBoundary =
  representationCarrierBoundary false false false false true true

record RepresentationCarrierReceipt : Set where
  constructor representationCarrierReceipt
  field
    label : String
    boundary : RepresentationCarrierBoundary
    observableEvidenceSeparatedFromLatentMechanism : Bool
    latentMechanismSeparatedFromNormativeClassification : Bool
    normativeClassificationSeparatedFromLegalConclusion : Bool

canonicalRepresentationCarrierReceipt : RepresentationCarrierReceipt
canonicalRepresentationCarrierReceipt =
  representationCarrierReceipt
    "representation carrier authority verification"
    canonicalRepresentationCarrierBoundary
    true true true
