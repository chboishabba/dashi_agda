module DASHI.Cognition.PNF.OperationalIR where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Cognition.PNF.EventAlgebra as PNF

data IRDomain : Set where
  legalDomain timelineDomain retrievalDomain memoryDomain nashiDomain : IRDomain
  genericSemanticDomain : IRDomain

data IRValidationState : Set where
  operationallyValid missingRequiredField supersededRule : IRValidationState
  blockedByException executionGateFailed insufficientForDomain : IRValidationState

data ExecutionOutcome : Set where
  executed refused insufficient superseded : ExecutionOutcome

record DomainIR : Set where
  constructor domainIR
  field
    domain : IRDomain
    sourcePNF : PNF.ResolvedPNF
    actor action object modality condition exception : String
    jurisdictionOrFrame : String
    operationalQualifiers : List String
    validationState : IRValidationState
    projectionReceipt : String

open DomainIR public

projectResolvedPNF :
  IRDomain →
  PNF.ResolvedPNF →
  String → String → String → String → String → String → String →
  List String →
  IRValidationState →
  String →
  DomainIR
projectResolvedPNF domain p actor action object modality condition exception frame qualifiers state receipt =
  domainIR domain p actor action object modality condition exception frame qualifiers state receipt

record IRExecutionReceipt : Set where
  constructor irExecutionReceipt
  field
    inputIR : DomainIR
    ruleOrQueryId : String
    emittedOutput : String
    outcome : ExecutionOutcome
    executionReasonChain : List String
    executionReceiptId : String

open IRExecutionReceipt public

record PNFIRProjectionLaw : Set where
  constructor pnfIRProjectionLaw
  field
    pnfSemanticallyRicher : Bool
    pnfSemanticallyRicherIsTrue : pnfSemanticallyRicher ≡ true
    irOperationallySharper : Bool
    irOperationallySharperIsTrue : irOperationallySharper ≡ true
    algebraRunsBeforeProjection : Bool
    algebraRunsBeforeProjectionIsTrue : algebraRunsBeforeProjection ≡ true
    invalidCandidateCannotConstructDomainIR : Bool

canonicalPNFIRProjectionLaw : PNFIRProjectionLaw
canonicalPNFIRProjectionLaw =
  pnfIRProjectionLaw true refl true refl true refl true

legalProjection :
  PNF.ResolvedPNF →
  String → String → String → String → String → String → String →
  DomainIR
legalProjection p actor action object modality condition exception jurisdiction =
  domainIR legalDomain p actor action object modality condition exception jurisdiction
    ("span-anchored" ∷ "rule-ready" ∷ [])
    operationallyValid
    "legal IR projected from resolved PNF"

timelineProjection :
  PNF.ResolvedPNF → String → String → String → DomainIR
timelineProjection p actor eventLabel effectiveTime =
  domainIR timelineDomain p actor eventLabel "" "" effectiveTime "" "timeline"
    ("publication-time" ∷ "effective-time" ∷ [])
    operationallyValid
    "timeline IR projected from resolved PNF"

retrievalProjection :
  PNF.ResolvedPNF → String → String → String → DomainIR
retrievalProjection p entity queryKey retrievalFrame =
  domainIR retrievalDomain p entity "retrieve" queryKey "" "" "" retrievalFrame
    ("index-key" ∷ "source-PNF-retained" ∷ [])
    operationallyValid
    "retrieval IR projected from resolved PNF"

memoryProjection :
  PNF.ResolvedPNF → String → String → String → DomainIR
memoryProjection p eventType valuationBand retrievalKey =
  domainIR memoryDomain p "memory" eventType retrievalKey valuationBand "" "" "memory"
    ("versioned" ∷ "semantic-content-retained" ∷ [])
    operationallyValid
    "memory IR projected from resolved PNF"

nashiProjection :
  PNF.ResolvedPNF → String → String → String → DomainIR
nashiProjection p entity eventType mechanismStatus =
  domainIR nashiDomain p entity eventType "market evidence candidate" "" "" "" mechanismStatus
    ("no-lookahead" ∷ "mechanism-not-promoted-by-text" ∷ [])
    operationallyValid
    "NASHI evidence IR projected from resolved PNF"
