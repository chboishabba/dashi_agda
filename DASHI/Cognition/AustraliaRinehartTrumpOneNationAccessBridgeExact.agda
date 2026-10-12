module DASHI.Cognition.AustraliaRinehartTrumpOneNationAccessBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Governance.HansonOneNationPoliticalEcologyExact as HansonEcology
import DASHI.Governance.HansonIsraelJewishPluralitySurveillanceGrammarExact as HansonBoundary
import DASHI.Cognition.EpsteinAustraliaEliteNetworkAcquisitionExact as AustraliaEpstein
import DASHI.Cognition.TrumpMarALagoBannonBridgeExact as TrumpBannon

------------------------------------------------------------------------
-- AUSTRALIA / RINEHART / TRUMP / ONE NATION ACCESS-BROKERAGE BRIDGE
--
-- This owner deliberately sits adjacent to, not inside, the direct Epstein-
-- Australia graph. Contemporary Rinehart -> Trump access -> One Nation donor
-- redirection is independently relevant political-finance/access evidence, but
-- it does not manufacture a Gina Rinehart <-> Jeffrey Epstein relationship.
--
-- Existing Hanson political-ecology and Trump-alignment noncollapse machinery
-- is reused so donation, access, ideology, policy capture and coordination stay
-- separate typed claims.
------------------------------------------------------------------------

data AustraliaTrumpAccessEdgeKind : Set where
  rinehartTrumpAccessBrokerage : AustraliaTrumpAccessEdgeKind
  oneNationDonorSwitch : AustraliaTrumpAccessEdgeKind
  marALagoTrumpMeeting : AustraliaTrumpAccessEdgeKind
  rinehartHansonTravelSupport : AustraliaTrumpAccessEdgeKind
  rinehartAssociateDonationSupport : AustraliaTrumpAccessEdgeKind
  oneNationNRAForeignFundingSolicitation : AustraliaTrumpAccessEdgeKind
  bannonPalmerInfluenceClaim : AustraliaTrumpAccessEdgeKind
  rinehartEpsteinNoPaidDirectEdge : AustraliaTrumpAccessEdgeKind

record AustraliaTrumpAccessReceipt : Set where
  constructor australia-trump-access-receipt
  field
    edgeKind : AustraliaTrumpAccessEdgeKind
    sourceDescription : String
    relationEstablished : Bool
    sourceAttributedOrDisputed : Bool
    wrongdoingEstablishedByThisReceipt : Bool
    directRinehartEpsteinRelationshipEstablishedByThisReceipt : Bool
open AustraliaTrumpAccessReceipt public

rinehartTrumpBrokerageReceipt : AustraliaTrumpAccessReceipt
rinehartTrumpBrokerageReceipt = australia-trump-access-receipt
  rinehartTrumpAccessBrokerage
  "Guardian Australia 2026 reports Gina Rinehart used her Mar-a-Lago/Trump access as part of a political-fundraising arrangement that redirected former Liberal donors toward One Nation. This establishes access brokerage, not bribery or policy capture."
  true false false false

oneNationDonorSwitchReceipt : AustraliaTrumpAccessReceipt
oneNationDonorSwitchReceipt = australia-trump-access-receipt
  oneNationDonorSwitch
  "Guardian/The Australian 2026 report that three fund managers were associated with a combined AUD 300k One Nation donation commitment after a Rinehart-hosted Trump/Mar-a-Lago access offer. Exact donor/payment records remain independently resolvable."
  true false false false

marALagoMeetingReceipt : AustraliaTrumpAccessReceipt
marALagoMeetingReceipt = australia-trump-access-receipt
  marALagoTrumpMeeting
  "Guardian Australia reports Ben Cleary and Doug Tynan met Donald Trump with Gina Rinehart at Mar-a-Lago on 26 March 2026; Pauline Hanson was campaigning in South Australia and was not at that dinner."
  true false false false

rinehartHansonTravelSupportReceipt : AustraliaTrumpAccessReceipt
rinehartHansonTravelSupportReceipt = australia-trump-access-receipt
  rinehartHansonTravelSupport
  "Guardian Australia reports multiple Rinehart-funded or supplied flights involving Hanson, including US travel connected to CPAC and Mar-a-Lago events; reporting also records Senate gift-declaration issues."
  true false false false

rinehartAssociateDonationReceipt : AustraliaTrumpAccessReceipt
rinehartAssociateDonationReceipt = australia-trump-access-receipt
  rinehartAssociateDonationSupport
  "Guardian Australia reports Rinehart associates donated an aircraft worth over AUD 1.5m and donations totalling AUD 2m to One Nation. This owner does not promote questions about proxy donation into a finding that Rinehart supplied the underlying money."
  true true false false

oneNationNRAReceipt : AustraliaTrumpAccessReceipt
oneNationNRAReceipt = australia-trump-access-receipt
  oneNationNRAForeignFundingSolicitation
  "ABC/Al Jazeera 2019 undercover reporting records James Ashby and Steve Dickson seeking large US gun-lobby/Koch-linked political funding while discussing gun-law and political-influence strategy. The reporting says no evidence showed the sought foreign money was actually provided."
  true false false false

bannonPalmerReceipt : AustraliaTrumpAccessReceipt
bannonPalmerReceipt = australia-trump-access-receipt
  bannonPalmerInfluenceClaim
  "A DOJ-released 2019 text records Steve Bannon claiming to Epstein that he had Clive Palmer run AUD 60m anti-China and anti-climate-change advertising. Palmer denies Bannon directed the campaign and denies an Epstein relationship. This pays the existence of Bannon's claim, not its truth."
  true true false false

rinehartEpsteinBoundaryReceipt : AustraliaTrumpAccessReceipt
rinehartEpsteinBoundaryReceipt = australia-trump-access-receipt
  rinehartEpsteinNoPaidDirectEdge
  "The contemporary Rinehart-Trump-One Nation access graph does not establish a direct Gina Rinehart-Jeffrey Epstein relationship. The existing Australia-Epstein owner likewise has no paid direct Rinehart-Epstein edge."
  false false false false

------------------------------------------------------------------------
-- Existing-owner availability / noncollapse receipts.
------------------------------------------------------------------------

existingAustraliaOwnerKeepsRinehartEpsteinUnpaid :
  AustraliaEpstein.ginaRinehartDirectRelationshipPaid
    AustraliaEpstein.canonicalAustraliaAcquisitionBoundary ≡ false
existingAustraliaOwnerKeepsRinehartEpsteinUnpaid = refl

hansonPoliticalEcologyAvailable : Bool
hansonPoliticalEcologyAvailable = true

hansonTrumpAlignmentNoncollapseAvailable : Bool
hansonTrumpAlignmentNoncollapseAvailable = true

trumpBannonBridgeAvailable : Bool
trumpBannonBridgeAvailable = true

------------------------------------------------------------------------
-- Canonical boundary.
------------------------------------------------------------------------

record AustraliaTrumpPoliticalFinanceBoundary : Set where
  constructor australia-trump-political-finance-boundary
  field
    rinehartTrumpAccessBrokeragePaid : Bool
    oneNationDonorRedirectionPaid : Bool
    marchMarALagoMeetingPaid : Bool
    hansonPresentAtMarchTrumpDinner : Bool
    rinehartPoliticalSupportForHansonPaid : Bool
    oneNationUSGunLobbySolicitationPaid : Bool
    bannonClaimedPalmerInfluencePaid : Bool
    palmerBannonOperationalInfluenceEstablished : Bool
    rinehartDirectEpsteinRelationshipPaid : Bool
    accessTransactionProvesPolicyCapture : Bool
    sharedTrumpAlignmentProvesCoordination : Bool
open AustraliaTrumpPoliticalFinanceBoundary public

canonicalAustraliaTrumpPoliticalFinanceBoundary :
  AustraliaTrumpPoliticalFinanceBoundary
canonicalAustraliaTrumpPoliticalFinanceBoundary =
  australia-trump-political-finance-boundary
    true true true false true true true false false false false

------------------------------------------------------------------------
-- Attribution / promotion firewalls.
------------------------------------------------------------------------

data AccessBrokerageImpliesBribery : Set where
data DonationImpliesPolicyCapture : Set where
data AssociateDonationImpliesRinehartSourceFunds : Set where
data SharedTrumpAlignmentImpliesCoordination : Set where
data BannonClaimImpliesPalmerDirection : Set where
data TrumpAccessImpliesEpsteinRelationship : Set where
data HistoricalForeignSolicitationImpliesCurrentCoordination : Set where

accessBrokerageDoesNotByItselfCreateBribery : AccessBrokerageImpliesBribery → ⊥
accessBrokerageDoesNotByItselfCreateBribery ()

donationDoesNotCreatePolicyCapture : DonationImpliesPolicyCapture → ⊥
donationDoesNotCreatePolicyCapture ()

associateDonationDoesNotProveRinehartSourceFunds :
  AssociateDonationImpliesRinehartSourceFunds → ⊥
associateDonationDoesNotProveRinehartSourceFunds ()

sharedTrumpAlignmentDoesNotCreateCoordination : SharedTrumpAlignmentImpliesCoordination → ⊥
sharedTrumpAlignmentDoesNotCreateCoordination ()

bannonClaimDoesNotCreatePalmerDirection : BannonClaimImpliesPalmerDirection → ⊥
bannonClaimDoesNotCreatePalmerDirection ()

trumpAccessDoesNotCreateEpsteinRelationship : TrumpAccessImpliesEpsteinRelationship → ⊥
trumpAccessDoesNotCreateEpsteinRelationship ()

historicalSolicitationDoesNotCreateCurrentCoordination :
  HistoricalForeignSolicitationImpliesCurrentCoordination → ⊥
historicalSolicitationDoesNotCreateCurrentCoordination ()
