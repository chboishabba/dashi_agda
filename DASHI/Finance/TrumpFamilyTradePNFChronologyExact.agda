module DASHI.Finance.TrumpFamilyTradePNFChronologyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.EventAlgebra as Event
import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas
import DASHI.Finance.TrumpFamilyTradePNFBridgeExact as Bridge

record ExactTradeClaimPNFChronology
    (claim : Atlas.TradeEvidenceClaim) : Set₁ where
  constructor exact-trade-claim-pnf-chronology
  field
    binding : Bridge.TradeClaimPNFBinding claim
    eventDateMatches :
      Event.eventTime (Bridge.event binding) ≡ Atlas.eventDate claim
    publicationDateMatches :
      Event.publicationTime (Bridge.event binding) ≡ Atlas.disclosureDate claim
    observationCutReference : String
    ingestionCutReference : String

open ExactTradeClaimPNFChronology public

data FilingBackdatesPublicKnowledgePermission : Set where
data FamilyRelationBackdatesKnowledgePermission : Set where
data EventDateMeansDisclosureDatePermission : Set where
data LaterDisclosureMeansEarlierMotivePermission : Set where

filingDoesNotBackdatePublicKnowledge :
  FilingBackdatesPublicKnowledgePermission → ⊥
filingDoesNotBackdatePublicKnowledge ()

familyRelationDoesNotBackdateKnowledge :
  FamilyRelationBackdatesKnowledgePermission → ⊥
familyRelationDoesNotBackdateKnowledge ()

eventDateDoesNotMeanDisclosureDate :
  EventDateMeansDisclosureDatePermission → ⊥
eventDateDoesNotMeanDisclosureDate ()

laterDisclosureDoesNotRevealEarlierMotive :
  LaterDisclosureMeansEarlierMotivePermission → ⊥
laterDisclosureDoesNotRevealEarlierMotive ()

record TradeInformationCutWitness
    (claim : Atlas.TradeEvidenceClaim)
    (time : String) : Set₁ where
  constructor trade-information-cut-witness
  field
    chronology : ExactTradeClaimPNFChronology claim
    AdmissibleAtCut : Set
    admissibleAtCut : AdmissibleAtCut
    cutReference : String

open TradeInformationCutWitness public

record TrumpFamilyTradePNFChronologyBoundary : Set where
  constructor trump-family-trade-pnf-chronology-boundary
  field
    eventAndDisclosureTimeAreSeparate : Bool
    exactBindingPaysBothTimeCoordinates : Bool
    disclosureDoesNotBackdatePublicKnowledge : Bool
    familyRelationDoesNotTransportKnowledgeBackward : Bool
    laterDisclosureDoesNotRevealEarlierMotive : Bool
    eventStudyRequiresPointInTimeAdmissibilityWitness : Bool

canonicalTrumpFamilyTradePNFChronologyBoundary :
  TrumpFamilyTradePNFChronologyBoundary
canonicalTrumpFamilyTradePNFChronologyBoundary =
  trump-family-trade-pnf-chronology-boundary true true true true true true
