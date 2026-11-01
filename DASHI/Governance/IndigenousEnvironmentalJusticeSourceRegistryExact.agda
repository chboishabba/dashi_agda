module DASHI.Governance.IndigenousEnvironmentalJusticeSourceRegistryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record SourceReference : Set where
  constructor sourceReference
  field
    authors : String
    title : String
    venue : String
    year : Nat
    identifierKind : String
    identifier : String
    sourceClass : String
    boundedRole : String

open SourceReference public

steffensen2020 : SourceReference
steffensen2020 = sourceReference
  "Victor Steffensen"
  "Fire Country: How Indigenous Fire Management Could Help Save Australia"
  "Hardie Grant Travel"
  2020
  "ISBN"
  "9781741177268"
  "Indigenous-authored primary book / practitioner account"
  "source for living cultural-fire knowledge and land-reading practice; does not by itself determine authority for every Country"

firesticks2020 : SourceReference
firesticks2020 = sourceReference
  "Firesticks Alliance Indigenous Corporation"
  "Submission 0906 to the NSW Independent Bushfire Inquiry"
  "NSW Government Bushfire Inquiry"
  2020
  "stable institutional submission"
  "0906-Firesticks-Alliance-Indigenous-Corporation-20200522"
  "First Nations-led institutional submission"
  "source for Country-specific cultural-fire authority/protocol and Indigenous-led cultural burning; quoted claims remain bounded to the submission"

ipccWGII2022 : SourceReference
ipccWGII2022 = sourceReference
  "Intergovernmental Panel on Climate Change, Working Group II"
  "Climate Change 2022: Impacts, Adaptation and Vulnerability"
  "IPCC Sixth Assessment Report"
  2022
  "institutional report"
  "IPCC AR6 WGII"
  "international assessment report"
  "source for high-confidence value of Indigenous/local/scientific knowledge in inclusive adaptation planning and for Indigenous-contributing-author participation in Chapter 14"

sherpa2025 : SourceReference
sherpa2025 = sourceReference
  "Pasang Yangjee Sherpa"
  "Relevance of the Sixth IPCC Assessment Report to Indigenous lived realities"
  "AlterNative 21(3):463-471"
  2025
  "DOI"
  "10.1177/11771801251362621"
  "Indigenous-authored peer-reviewed systematic audit"
  "source for uneven AR6 Indigenous representation and knowledge-base critique across WGI/WGII/WGIII; does not imply IPCC reports are wholly unusable"

nativeTitleAct1993 : SourceReference
nativeTitleAct1993 = sourceReference
  "Commonwealth of Australia"
  "Native Title Act 1993 (Cth)"
  "Federal Register of Legislation"
  1993
  "Act"
  "C2004A04665"
  "primary legislation"
  "source for s223 native-title definition and ss55-57 prescribed-body-corporate machinery; legal recognition is not identified with community sovereignty"

oricRntbc : SourceReference
oricRntbc = sourceReference
  "Office of the Registrar of Indigenous Corporations"
  "Native title and RNTBCs"
  "Australian Government"
  2026
  "institutional guidance"
  "ORIC native-title-and-rntbcs"
  "official administrative guidance"
  "source for RNTBC/PBC role in holding or managing native-title rights on behalf of common-law holders and Traditional Owners"

iachr2021 : SourceReference
iachr2021 = sourceReference
  "Inter-American Commission on Human Rights"
  "Resolution 88/2021: Precautionary Measures No. 405-09 and 112-16"
  "Organization of American States"
  2021
  "official resolution"
  "IACHR Resolution 88/2021"
  "inter-governmental human-rights decision"
  "source for continuing precautionary-measures implementation concerning Berta Caceres' family, COPINH members and others; live protection matter"

caceresObserverMission2019 : SourceReference
caceresObserverMission2019 = sourceReference
  "International Observer Mission / FIDH-DPLF partners"
  "State of Honduras Remains Indebted for Murder of Berta Caceres"
  "trial-observer report reproducing Honduran sentencing finding"
  2019
  "stable legal-observer document"
  "DPLF 12_05_19 final English sentence report"
  "judicial-process observation / institutional documentation"
  "source for reported trial finding that the murder was planned with knowledge and consent of DESA executives; not a complete adjudication of every alleged mastermind"

copinhVictim2021 : SourceReference
copinhVictim2021 = sourceReference
  "FIDH and member organisations"
  "Honduras: COPINH recognized as victim in corruption trial"
  "FIDH"
  2021
  "institutional legal-process report"
  "FIDH 2021-08-31 COPINH victim recognition"
  "human-rights institutional documentation"
  "source for Honduran Constitutional Chamber recognition of Rio Blanco Lenca community through COPINH as victims in the Gualcarque corruption case"

navdanya2012 : SourceReference
navdanya2012 = sourceReference
  "Navdanya International and Seed Freedom contributors"
  "Seed Freedom: A Global Citizens' Report"
  "Navdanya International"
  2012
  "institutional primary report"
  "Seed Freedom Global Report 2012"
  "movement/institutional primary source"
  "source for seed saving/exchange, biodiversity, food security, commons and seed-sovereignty framing; not an empirical universal yield theorem"

record SourceBoundary : Set where
  constructor sourceBoundary
  field
    institutionalSourceTransfersUniversalAuthority : Bool
    institutionalSourceTransfersUniversalAuthorityIsFalse : institutionalSourceTransfersUniversalAuthority ≡ false
    legalRecognitionEqualsCommunitySovereignty : Bool
    legalRecognitionEqualsCommunitySovereigntyIsFalse : legalRecognitionEqualsCommunitySovereignty ≡ false
    movementDeclarationIsControlledCausalStudy : Bool
    movementDeclarationIsControlledCausalStudyIsFalse : movementDeclarationIsControlledCausalStudy ≡ false

canonicalSourceBoundary : SourceBoundary
canonicalSourceBoundary = sourceBoundary false refl false refl false refl
