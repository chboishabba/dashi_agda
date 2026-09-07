module DASHI.Law.SensibLawWrongTypeCausationElementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Law.LegalFactualCausationButForExact as ButFor
import DASHI.Law.SensibLawCausationQualifiedLiabilityBridgeExact as Qualified

------------------------------------------------------------------------
-- WRONGTYPE-FIRST FACTUAL CAUSATION ELEMENT
--
-- DASHI-original compiler/weld.
--
-- SensibLaw's ontology owns WrongType, StableId and WrongElementEvaluation.
-- This owner does not manufacture a new negligence ontology.  It lets an
-- authoritative legal-rule producer declare that one exact element of one
-- exact WrongType is a factual-causation element, and requires same-object
-- proofs back to the WrongType already carried by the applicability/violation
-- chain.
------------------------------------------------------------------------

data CausationElementKind : Set where
  ordinaryFactualCausationElement
  exceptionalFactualCausationElement
  scopeOfLiabilityElement
  causationElementKindUnresolved
  : CausationElementKind

record WrongTypeCausationElementDeclaration : Set₁ where
  constructor wrongTypeCausationElementDeclaration
  field
    wrongType : Ontology.WrongType
    elementId : String
    kind : CausationElementKind
    requirement : Qualified.CausationGateRequirement
    legalRuleReference : String
    legalSourceId : Ontology.StableId
    authorityReceipt : Set
    declarationReference : String

open WrongTypeCausationElementDeclaration public

------------------------------------------------------------------------
-- Weld the declared element to the exact WrongType in a ViolationReceipt.
------------------------------------------------------------------------

record ViolationWrongTypeCausationElementWeld
    (declaration : WrongTypeCausationElementDeclaration) : Set₁ where
  constructor violationWrongTypeCausationElementWeld
  field
    violation : Legal.ViolationReceipt

    sameWrongTypeId :
      Ontology.WrongType.wrongTypeId (wrongType declaration)
      ≡ Ontology.WrongType.wrongTypeId
          (Legal.wrongType (Legal.applicabilityReceipt violation))

    sameDefiningSystem :
      Ontology.WrongType.definingSystem (wrongType declaration)
      ≡ Ontology.WrongType.definingSystem
          (Legal.wrongType (Legal.applicabilityReceipt violation))

    elementEvaluation : Legal.WrongElementEvaluation
    evaluationMatchesWrongType :
      Legal.wrongTypeReference elementEvaluation
      ≡ Ontology.WrongType.wrongTypeId (wrongType declaration)
    evaluationMatchesElement :
      Legal.elementReference elementEvaluation ≡ elementId declaration

    weldReference : String

open ViolationWrongTypeCausationElementWeld public

------------------------------------------------------------------------
-- Exact payment of a factual-causation WrongType element.
------------------------------------------------------------------------

record FactualCausationElementPayment
    {declaration : WrongTypeCausationElementDeclaration}
    (weld : ViolationWrongTypeCausationElementWeld declaration) : Set₁ where
  constructor factualCausationElementPayment
  field
    question : ButFor.LegalButForQuestion
    factualCausation : ButFor.FactualCausationReceipt question
    proofReceipt : ButFor.CausationProofReceipt factualCausation

    paymentIsForFactualCausation :
      (kind declaration ≡ ordinaryFactualCausationElement)
      ⊎
      (kind declaration ≡ exceptionalFactualCausationElement)

    sameBreachOrViolationReceipt : Set
    sameParticularHarmReceipt : Set
    paymentReference : String

open FactualCausationElementPayment public

record ScopeElementPayment
    {declaration : WrongTypeCausationElementDeclaration}
    (weld : ViolationWrongTypeCausationElementWeld declaration) : Set₁ where
  constructor scopeElementPayment
  field
    question : ButFor.LegalButForQuestion
    factualCausation : ButFor.FactualCausationReceipt question
    scopeReceipt : ButFor.ScopeOfLiabilityReceipt factualCausation
    declarationIsScope : kind declaration ≡ scopeOfLiabilityElement
    sameParticularHarmReceipt : Set
    paymentReference : String

open ScopeElementPayment public

------------------------------------------------------------------------
-- Producer routing.  Missing legal elements request producers; producer
-- identity never itself closes the element.
------------------------------------------------------------------------

data CausationElementProducer : Set where
  ordinaryButForProducer
  exceptionalEstablishedPrinciplesProducer
  scopeResponsibilityProducer
  causationProducerUnresolved
  : CausationElementProducer

producerFor : CausationElementKind → CausationElementProducer
producerFor ordinaryFactualCausationElement = ordinaryButForProducer
producerFor exceptionalFactualCausationElement = exceptionalEstablishedPrinciplesProducer
producerFor scopeOfLiabilityElement = scopeResponsibilityProducer
producerFor causationElementKindUnresolved = causationProducerUnresolved

record MissingCausationElementDemand
    (declaration : WrongTypeCausationElementDeclaration) : Set where
  constructor missingCausationElementDemand
  field
    required : requirement declaration ≡ Qualified.causationRequired
    elementNotYetPaidReceipt : Set
    requestedProducer : CausationElementProducer
    requestedProducerIsCorrect : requestedProducer ≡ producerFor (kind declaration)
    demandReference : String

open MissingCausationElementDemand public

------------------------------------------------------------------------
-- Wrong-payment diagnostics: these are category mismatches, not mere absence.
------------------------------------------------------------------------

data CausationPaymentMismatch : Set where
  scopeOfferedForFactualCausation
  factualCausationOfferedForScope
  parserCandidateOfferedAsElementPayment
  differentWrongTypeOffered
  differentElementOffered
  : CausationPaymentMismatch

record RejectedCausationElementPayment : Set where
  constructor rejectedCausationElementPayment
  field
    mismatch : CausationPaymentMismatch
    expectedWrongType : Ontology.StableId
    expectedElement : String
    offeredReference : String
    rejectionReference : String

open RejectedCausationElementPayment public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CulpabilityNegligentAutomaticallyHasCausationElement : Set where
data SameCulpabilityAutomaticallySameWrongType : Set where
data SameWrongTypeAutomaticallySameElement : Set where
data ProducerExistsAutomaticallyPaysElement : Set where
data ScopePaymentCanPayFactualElement : Set where
data FactualPaymentCanPayScopeElement : Set where
data ParserCanDeclareWrongTypeElementRequirement : Set where

negligentCulpabilityDoesNotAutoDeclareCausationElement :
  CulpabilityNegligentAutomaticallyHasCausationElement → ⊥
negligentCulpabilityDoesNotAutoDeclareCausationElement ()

sameCulpabilityDoesNotIdentifyWrongType :
  SameCulpabilityAutomaticallySameWrongType → ⊥
sameCulpabilityDoesNotIdentifyWrongType ()

sameWrongTypeDoesNotIdentifyElement :
  SameWrongTypeAutomaticallySameElement → ⊥
sameWrongTypeDoesNotIdentifyElement ()

producerExistenceDoesNotPayElement :
  ProducerExistsAutomaticallyPaysElement → ⊥
producerExistenceDoesNotPayElement ()

scopeCannotSilentlyPayFactualCausation :
  ScopePaymentCanPayFactualElement → ⊥
scopeCannotSilentlyPayFactualCausation ()

factualCausationCannotSilentlyPayScope :
  FactualPaymentCanPayScopeElement → ⊥
factualCausationCannotSilentlyPayScope ()

parserCannotDeclareWrongTypeLegalRequirement :
  ParserCanDeclareWrongTypeElementRequirement → ⊥
parserCannotDeclareWrongTypeLegalRequirement ()

record WrongTypeCausationBoundary : Set where
  constructor wrongTypeCausationBoundary
  field
    causationRequirementIsWrongTypeElementIndexed : Bool
    causationRequirementIsWrongTypeElementIndexedIsTrue :
      causationRequirementIsWrongTypeElementIndexed ≡ true
    sameObjectWeldRequired : Bool
    sameObjectWeldRequiredIsTrue : sameObjectWeldRequired ≡ true
    producerIdentityClosesElement : Bool
    producerIdentityClosesElementIsFalse : producerIdentityClosesElement ≡ false
    factualCausationEqualsScopeElement : Bool
    factualCausationEqualsScopeElementIsFalse :
      factualCausationEqualsScopeElement ≡ false

canonicalWrongTypeCausationBoundary : WrongTypeCausationBoundary
canonicalWrongTypeCausationBoundary =
  wrongTypeCausationBoundary true refl true refl false refl false refl
