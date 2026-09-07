module DASHI.Biology.Agriculture.HungriaBiologicalNitrogenFixationSourceAtlas where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE / ATTRIBUTION BOUNDARY
--
-- This atlas records what each external source is licensed to establish.
-- It does not attribute DASHI's typed carrier design, no-go theorems, or
-- cross-source synthesis to Mariangela Hungria or her coauthors.
--
-- Repository rule used here:
--   external source claim != later interpretation
--   external source claim != DASHI formal reconstruction
--   cross-source inference   != source quotation
--   DASHI theorem           != externally reported empirical result
--   source receipt          != stronger promotion receipt
--
-- Exact metadata is retained where available.  No DOI is invented for
-- sources for which the surfaced record does not provide one.
------------------------------------------------------------------------

data SourceAuthority : Set where
  peerReviewedExperiment : SourceAuthority
  peerReviewedSynthesis : SourceAuthority
  peerReviewedEconomicModel : SourceAuthority
  institutionalRetrospective : SourceAuthority
  institutionalNewsCarrier : SourceAuthority

record BNFSource : Set where
  constructor bnfSource
  field
    authors : String
    title : String
    venueOrPublisher : String
    year : Nat
    identifier : String
    authority : SourceAuthority
    importedRole : String
    excludedPromotion : String

open BNFSource public

nishiHungria1996 : BNFSource
nishiHungria1996 =
  bnfSource
    "Catalina Y. Masuda Nishi; Mariangela Hungria"
    "Effects of soybean [Glycine max (L.) Merrill] inoculation in a soil with established population of Bradyrhizobium with strains SEMIA 566, 586, 587, 5019, 5079 and 5080"
    "Pesquisa Agropecuaria Brasileira 31(5):359-368"
    1996
    "DOI 10.1590/S1678-3921.pab1996.v31.4492"
    peerReviewedExperiment
    "Three field experiments; inoculated Bradyrhizobium strains established in the rhizosphere; reported soybean yield increases up to 420 kg/ha and higher grain N relative to a non-inoculated N-fertilized treatment"
    "Does not establish a universal yield gain, universal fertilizer replacement, universal inoculant cost, or a causal claim outside the reported experimental conditions"

hungriaMendes2015 : BNFSource
hungriaMendes2015 =
  bnfSource
    "Mariangela Hungria; Ieda Carvalho Mendes"
    "Nitrogen Fixation with Soybean: The Perfect Symbiosis?"
    "Biological Nitrogen Fixation, chapter 99, Wiley"
    2015
    "DOI 10.1002/9781119053095.ch99"
    peerReviewedSynthesis
    "Synthesis of soybean biological nitrogen fixation; reports South American high-yield soybean production without N fertilizer and consistent benefits from annual reinoculation"
    "Does not establish that every crop or every soybean field can eliminate synthetic N fertilizer"

fukamiEtAl2016 : BNFSource
fukamiEtAl2016 =
  bnfSource
    "Josiane Fukami; Marco Antonio Nogueira; Ricardo Silva Araujo; Mariangela Hungria"
    "Accessing inoculation methods of maize and wheat with Azospirillum brasilense"
    "AMB Express 6:3"
    2016
    "DOI 10.1186/s13568-015-0171-y"
    peerReviewedExperiment
    "Evaluation of Azospirillum brasilense inoculation methods for maize and wheat and practical constraints from seed-treatment pesticide incompatibility"
    "Does not establish that Azospirillum supplies the complete nitrogen requirement of non-legume crops"

hungria2020 : BNFSource
hungria2020 =
  bnfSource
    "Mariangela Hungria"
    "Seed pre-inoculation with Bradyrhizobium as time-optimizing option for large-scale soybean cropping systems"
    "Agronomy Journal"
    2020
    "DOI 10.1002/agj2.20392"
    peerReviewedExperiment
    "Four Brazilian field experiments evaluating liquid Bradyrhizobium pre-inoculation with cell protectors; reported symbiotic performance comparable to a peat-based inoculant"
    "Does not by itself establish nationwide economic savings, global CO2 avoidance, or every implementation detail of commercial inoculants"

tellesNogueiraHungria2023 : BNFSource
tellesNogueiraHungria2023 =
  bnfSource
    "Tiago Santos Telles; Marco Antonio Nogueira; Mariangela Hungria"
    "Economic value of biological nitrogen fixation in soybean crops in Brazil"
    "Environmental Technology & Innovation 31:103158"
    2023
    "DOI 10.1016/j.eti.2023.103158"
    peerReviewedEconomicModel
    "Avoided-cost and greenhouse-gas accounting model for Brazilian soybean BNF; source-owned 2019-2020 outputs include USD 15.2 billion avoided urea cost and 183 million Mg CO2-e mitigated"
    "Does not establish that later 2024/2025 headline values are a literal replay of the same model with an identified updated input vintage"

embrapa2025PrizeNews : BNFSource
embrapa2025PrizeNews =
  bnfSource
    "Embrapa institutional news publication"
    "Mariangela Hungria to receive the World Food Prize, the Nobel Prize for Agriculture, in the United States"
    "Embrapa Portal / Embrapa Soja"
    2025
    "No DOI assigned; Embrapa news item dated 16 October 2025"
    institutionalNewsCarrier
    "Reports estimated 2024 savings of about USD 25 billion from avoided nitrogen fertilizer and quotes Hungria stating mitigation of more than 230 million tonnes CO2-equivalent in 2024"
    "Does not itself recover the unpublished calculation workbook, exact 2024 input vector, or proof that every sentence in the institutional article is personally authored by Hungria"

worldFoodPrize2025 : BNFSource
worldFoodPrize2025 =
  bnfSource
    "World Food Prize Foundation"
    "2025 Laureate: Mariangela Hungria"
    "World Food Prize Foundation"
    2025
    "No DOI assigned; institutional laureate biography"
    institutionalRetrospective
    "Retrospective account of Hungria's multi-decade research programme, strain selection, stress testing, inoculant development, scale of adoption, and prize rationale; repeats roughly USD 25 billion annual savings, 230 million metric tons CO2-equivalent avoided, and more than 40 million hectares of adoption"
    "Institutional retrospective estimates are not substituted for the primary experimental or model evidence and are not treated as a single paper proving every economic or emissions number"

canonicalHungriaBNFSources : List BNFSource
canonicalHungriaBNFSources =
  nishiHungria1996
  ∷ hungriaMendes2015
  ∷ fukamiEtAl2016
  ∷ hungria2020
  ∷ tellesNogueiraHungria2023
  ∷ embrapa2025PrizeNews
  ∷ worldFoodPrize2025
  ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ xs) = suc (listCount xs)

sourceCountIsSeven : listCount canonicalHungriaBNFSources ≡ 7
sourceCountIsSeven = refl
