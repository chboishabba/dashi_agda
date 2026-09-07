module DASHI.Law.AustralianColonialPrimarySourceAttributionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Primary-source attribution for colonial classification / sovereignty claims.
------------------------------------------------------------------------

data PrimarySourceRole : Set where
  privyCouncilHolding
  highCourtHolding
  firstNationsPoliticalStatement
  highCourtCurrentDoctrine
  dashiSynthesis : PrimarySourceRole

data PrimaryProposition : Set where
  cooperClassifiedNSWAsSettledWithoutSettledLaw
  cooperUsedClassificationToReceiveEnglishLaw
  maboRejectedEnlargedTerraNulliusForNativeTitle
  maboRecognisedPreExistingNativeTitleRatherThanCreatingIt
  uluruStatesSovereigntyNeverCeded
  loveRecognisesDistinctConstitutionalConnectionToCountry
  classificationOperationallyChangedAvailableLegalConsequences
  semanticReclassificationWasNecessaryToSettledColonyReceptionLogic : PrimaryProposition

record PrimaryReceipt : Set where
  constructor primaryReceipt
  field
    proposition : PrimaryProposition
    sourceRole : PrimarySourceRole
    sourceReference : String
    boundedDescription : String

open PrimaryReceipt public

cooperSettledReceipt : PrimaryReceipt
cooperSettledReceipt = primaryReceipt
  cooperClassifiedNSWAsSettledWithoutSettledLaw privyCouncilHolding
  "Cooper v Stuart [1889] UKPC 16, paras 11-13"
  "The Privy Council classified New South Wales as practically unoccupied, without settled inhabitants or settled law, and placed it in the settled-colony category."

cooperReceptionReceipt : PrimaryReceipt
cooperReceptionReceipt = primaryReceipt
  cooperUsedClassificationToReceiveEnglishLaw privyCouncilHolding
  "Cooper v Stuart [1889] UKPC 16, paras 11-13"
  "The settled-colony classification was used to determine that applicable English law prevailed in the colony and governed land transactions; this is an operational legal consequence of the classification."

maboRejectionReceipt : PrimaryReceipt
maboRejectionReceipt = primaryReceipt
  maboRejectedEnlargedTerraNulliusForNativeTitle highCourtHolding
  "Mabo v Queensland (No 2) [1992] HCA 23"
  "The High Court rejected the enlarged terra-nullius assumptions that had denied recognition of pre-existing Indigenous land rights under traditional law and custom."

maboPreExistingReceipt : PrimaryReceipt
maboPreExistingReceipt = primaryReceipt
  maboRecognisedPreExistingNativeTitleRatherThanCreatingIt highCourtHolding
  "Mabo v Queensland (No 2) [1992] HCA 23; later High Court statement in Yorta Yorta litigation"
  "Native title is treated as arising from pre-existing traditional law/custom and recognised by common law rather than created ex nihilo by Crown recognition."

uluruNeverCededPrimaryReceipt : PrimaryReceipt
uluruNeverCededPrimaryReceipt = primaryReceipt
  uluruStatesSovereigntyNeverCeded firstNationsPoliticalStatement
  "Uluru Statement from the Heart, 2017"
  "The Statement says First Nations sovereignty has never been ceded or extinguished and co-exists with Crown sovereignty; this is not attributed to the High Court."

loveConnectionReceipt : PrimaryReceipt
loveConnectionReceipt = primaryReceipt
  loveRecognisesDistinctConstitutionalConnectionToCountry highCourtCurrentDoctrine
  "Love v Commonwealth; Thoms v Commonwealth [2020] HCA 3"
  "The High Court majority held Aboriginal Australians within the relevant test are beyond the aliens power, relying on a special cultural, historical and spiritual connection with Australian territory recognised by common law."

classificationOperationalSynthesis : PrimaryReceipt
classificationOperationalSynthesis = primaryReceipt
  classificationOperationallyChangedAvailableLegalConsequences dashiSynthesis
  "DASHI synthesis over Cooper, Mabo and Love"
  "The legal category assigned to Indigenous people/Country altered which law, land relations and state powers the colonial/constitutional legal system treated as available; this is a DASHI synthesis from primary holdings, not a quotation from any one court."

necessaryReceptionSynthesis : PrimaryReceipt
necessaryReceptionSynthesis = primaryReceipt
  semanticReclassificationWasNecessaryToSettledColonyReceptionLogic dashiSynthesis
  "DASHI synthesis over Cooper v Stuart [1889] UKPC 16 paras 11-13 and Mabo [1992] HCA 23"
  "Within the settled-colony reception logic actually articulated in Cooper, classifying NSW as lacking settled inhabitants/law was not incidental description: it was a premise used to determine reception of English law. This does not establish every colonial actor's subjective motive."

record PrimaryAttributionBoundary : Set where
  constructor primaryAttributionBoundary
  field
    cooperSaysFirstNationsActuallyHadNoLaw : Bool
    cooperSaysFirstNationsActuallyHadNoLawIsFalse : cooperSaysFirstNationsActuallyHadNoLaw ≡ false
    uluruNeverCededIsHighCourtHolding : Bool
    uluruNeverCededIsHighCourtHoldingIsFalse : uluruNeverCededIsHighCourtHolding ≡ false
    maboInvalidatedCrownSovereignty : Bool
    maboInvalidatedCrownSovereigntyIsFalse : maboInvalidatedCrownSovereignty ≡ false
    dashiNecessaryPremiseSynthesisIsPrivyCouncilQuote : Bool
    dashiNecessaryPremiseSynthesisIsPrivyCouncilQuoteIsFalse : dashiNecessaryPremiseSynthesisIsPrivyCouncilQuote ≡ false

canonicalPrimaryAttributionBoundary : PrimaryAttributionBoundary
canonicalPrimaryAttributionBoundary = primaryAttributionBoundary false refl false refl false refl false refl
