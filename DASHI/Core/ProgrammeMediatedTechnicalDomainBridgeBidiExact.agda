module DASHI.Core.ProgrammeMediatedTechnicalDomainBridgeBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TechnicalDependencyHypergraphExact as H

------------------------------------------------------------------------
-- PROGRAMME-MEDIATED TECHNICAL DOMAIN BRIDGE — BIDI KERNEL
--
-- A broad similarity between two technical domains is not enough. Promotion
-- requires a source-backed programme whose own technical description contains
-- both domains on the same literal programme receipt.
------------------------------------------------------------------------

record ProgrammeDomainBridge : Set₁ where
  constructor programme-domain-bridge
  field
    programme : H.TechnicalNode
    leftDomain : H.TechnicalNode
    rightDomain : H.TechnicalNode
    programmeReceipt : H.TechnicalHyperedge

    sameObjectEndpoints :
      H.endpoints programmeReceipt ≡
      programme ∷ leftDomain ∷ rightDomain ∷ []

    receiptUsesTechnology :
      H.edgeKind programmeReceipt ≡ H.programmeUsesTechnology

    receiptIsOfficial :
      H.edgeStrength programmeReceipt ≡ H.officialProgrammeReceipt

    receiptSurvives :
      H.quotientDisposition programmeReceipt ≡ H.survivesTechnicalQuotient

    sourceReference : String
    boundedBridgeReading : String

open ProgrammeDomainBridge public

------------------------------------------------------------------------
-- Reverse/BIDI consumer obligations.
------------------------------------------------------------------------

record DomainBridgeConsumerObligations : Set₁ where
  constructor domain-bridge-consumer-obligations
  field
    requiredProgramme : H.TechnicalNode
    requiredLeftDomain : H.TechnicalNode
    requiredRightDomain : H.TechnicalNode
    requireSameProgrammeObject : Bool
    requireSameProgrammeObjectIsTrue :
      requireSameProgrammeObject ≡ true
    requireOfficialProgrammeReceipt : Bool
    requireOfficialProgrammeReceiptIsTrue :
      requireOfficialProgrammeReceipt ≡ true

open DomainBridgeConsumerObligations public

obligationsOf : ProgrammeDomainBridge → DomainBridgeConsumerObligations
obligationsOf bridge =
  domain-bridge-consumer-obligations
    (programme bridge)
    (leftDomain bridge)
    (rightDomain bridge)
    true refl
    true refl

------------------------------------------------------------------------
-- Exact forward promotion target.
------------------------------------------------------------------------

record PromotedTechnicalDomainBridge : Set₁ where
  constructor promoted-technical-domain-bridge
  field
    witness : ProgrammeDomainBridge
    noLongerSimilarityOnly : Bool
    noLongerSimilarityOnlyIsTrue : noLongerSimilarityOnly ≡ true
    survivesTechnicalQuotientViaProgramme : Bool
    survivesTechnicalQuotientViaProgrammeIsTrue :
      survivesTechnicalQuotientViaProgramme ≡ true

open PromotedTechnicalDomainBridge public

promote : ProgrammeDomainBridge → PromotedTechnicalDomainBridge
promote bridge =
  promoted-technical-domain-bridge bridge true refl true refl

------------------------------------------------------------------------
-- Authority firewall.
------------------------------------------------------------------------

record DomainBridgeAuthorityBoundary : Set where
  constructor domain-bridge-authority-boundary
  field
    bridgeImpliesSharedPerson : Bool
    bridgeImpliesSharedPersonIsFalse : bridgeImpliesSharedPerson ≡ false

    bridgeImpliesPersonWorkedOnProgramme : Bool
    bridgeImpliesPersonWorkedOnProgrammeIsFalse :
      bridgeImpliesPersonWorkedOnProgramme ≡ false

    bridgeImpliesPersonalContact : Bool
    bridgeImpliesPersonalContactIsFalse : bridgeImpliesPersonalContact ≡ false

    bridgeImpliesCommonEmployer : Bool
    bridgeImpliesCommonEmployerIsFalse : bridgeImpliesCommonEmployer ≡ false

    bridgeImpliesCommonSelector : Bool
    bridgeImpliesCommonSelectorIsFalse : bridgeImpliesCommonSelector ≡ false

    bridgeImpliesSharedAdversary : Bool
    bridgeImpliesSharedAdversaryIsFalse : bridgeImpliesSharedAdversary ≡ false

    bridgeImpliesCausalExplanation : Bool
    bridgeImpliesCausalExplanationIsFalse : bridgeImpliesCausalExplanation ≡ false

canonicalDomainBridgeAuthorityBoundary : DomainBridgeAuthorityBoundary
canonicalDomainBridgeAuthorityBoundary =
  domain-bridge-authority-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Cross-pollination firewall:
--
--     domain A -> generic bridge <- domain B
--
-- permits transfer of theorem shape / acquisition obligations, not transfer of
-- application evidence or person-level attribution.
------------------------------------------------------------------------

record BidiCrossPollinationBoundary : Set where
  constructor bidi-cross-pollination-boundary
  field
    sharedProgrammeBridgePermitsTheoremShapeReuse : Bool
    sharedProgrammeBridgePermitsTheoremShapeReuseIsTrue :
      sharedProgrammeBridgePermitsTheoremShapeReuse ≡ true

    foreignPersonReceiptDischargesLocalPersonReceipt : Bool
    foreignPersonReceiptDischargesLocalPersonReceiptIsFalse :
      foreignPersonReceiptDischargesLocalPersonReceipt ≡ false

canonicalBidiCrossPollinationBoundary : BidiCrossPollinationBoundary
canonicalBidiCrossPollinationBoundary =
  bidi-cross-pollination-boundary true refl false refl
