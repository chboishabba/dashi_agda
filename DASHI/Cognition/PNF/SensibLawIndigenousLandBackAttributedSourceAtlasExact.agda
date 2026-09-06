module DASHI.Cognition.PNF.SensibLawIndigenousLandBackAttributedSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Cognition.PNF.SensibLawIndigenousLandBackSourceAuthorityExact as Authority

------------------------------------------------------------------------
-- Canonical bibliographic metadata for the current LAND BACK / stewardship
-- evidence lane.  This is source identity/provenance only.  It does not import
-- source claims, proof, agreement, legal authority, scientific authority or
-- causal authority.
------------------------------------------------------------------------

denBraber2024Source : Attr.AttributedSource
denBraber2024Source = Attr.mkDOISource
  "Bowy den Braber; Johan A. Oldekop; Katie Devenish; Javier Godar; Christoph Nolte; Marina Schmoeller; Karl L. Evans"
  "Socio-economic and environmental trade-offs in Amazonian protected areas and Indigenous territories revealed by assessing competing land uses"
  "Nature Ecology & Evolution 8, 1482-1492"
  "2024"
  "10.1038/s41559-024-02458-w"
  "https://doi.org/10.1038/s41559-024-02458-w"
  Attr.academicArticleSource
  "peer-reviewed comparative evidence; metadata identity does not promote comparative estimates into universal causal claims"
  Attr.publicAttribution

baragwanathBayi2020Source : Attr.AttributedSource
baragwanathBayi2020Source = Attr.mkDOISource
  "Kathryn Baragwanath; Ella Bayi"
  "Collective property rights reduce deforestation in the Brazilian Amazon"
  "Proceedings of the National Academy of Sciences 117(34), 20495-20502"
  "2020"
  "10.1073/pnas.1917874117"
  "https://doi.org/10.1073/pnas.1917874117"
  Attr.academicArticleSource
  "peer-reviewed causal-design evidence for collective property rights and deforestation in the studied Brazilian Amazon setting"
  Attr.publicAttribution

baragwanathBayiShinde2023Source : Attr.AttributedSource
baragwanathBayiShinde2023Source = Attr.mkDOISource
  "Kathryn Baragwanath; Ella Bayi; Nilesh Shinde"
  "Collective property rights lead to secondary forest growth in the Brazilian Amazon"
  "Proceedings of the National Academy of Sciences 120(22), e2221346120"
  "2023"
  "10.1073/pnas.2221346120"
  "https://doi.org/10.1073/pnas.2221346120"
  Attr.academicArticleSource
  "peer-reviewed causal-design evidence for collective property rights and secondary-forest recovery in the studied setting"
  Attr.publicAttribution

probst2020Source : Attr.AttributedSource
probst2020Source = Attr.mkDOISource
  "Benedict Probst; Ariel BenYishay; Andreas Kontoleon; Tiago N. P. dos Reis"
  "Impacts of a large-scale titling initiative on deforestation in the Brazilian Amazon"
  "Nature Sustainability 3, 1019-1026"
  "2020"
  "10.1038/s41893-020-0537-2"
  "https://doi.org/10.1038/s41893-020-0537-2"
  Attr.academicArticleSource
  "property-level fixed-effects/event-study evidence about Terra Legal private titling; not an Indigenous collective-tenure proxy"
  Attr.publicAttribution

sze2022Source : Attr.AttributedSource
sze2022Source = Attr.mkDOISource
  "Jocelyne S. Sze; L. Roman Carrasco; Dylan Childs; David P. Edwards"
  "Reduced deforestation and degradation in Indigenous Lands pan-tropically"
  "Nature Sustainability 5, 123-130"
  "2022"
  "10.1038/s41893-021-00815-2"
  "https://doi.org/10.1038/s41893-021-00815-2"
  Attr.academicArticleSource
  "matched pan-tropical comparative evidence; not universal causal closure"
  Attr.publicAttribution

garnett2018Source : Attr.AttributedSource
garnett2018Source = Attr.mkDOISource
  "Stephen T. Garnett et al."
  "A spatial overview of the global importance of Indigenous lands for conservation"
  "Nature Sustainability 1, 369-374"
  "2018"
  "10.1038/s41893-018-0100-6"
  "https://doi.org/10.1038/s41893-018-0100-6"
  Attr.academicArticleSource
  "global spatial/descriptive evidence; author field deliberately uses et al. because this atlas does not claim its string is an exhaustive author list"
  Attr.publicAttribution

mortonNinomiya2023Source : Attr.AttributedSource
mortonNinomiya2023Source = Attr.mkDOISource
  "Melody E. Morton Ninomiya; Nicole Burns; Nathaniel J. Pollock; Nadia T. G. Green; Jessica Martin; Janice Linton; Jenny R. Rand; Laura Jane Brubacher; Arn Keeling; Alex Latta"
  "Indigenous communities and the mental health impacts of land dispossession related to industrial resource development: a systematic review"
  "The Lancet Planetary Health 7(6), e501-e517"
  "2023"
  "10.1016/S2542-5196(23)00079-7"
  "https://doi.org/10.1016/S2542-5196(23)00079-7"
  Attr.academicArticleSource
  "systematic-review evidence on dispossession-related mental-health impacts; inverse benefit magnitude is not inferred automatically"
  Attr.publicAttribution

gall2021Source : Attr.AttributedSource
gall2021Source = Attr.mkDOISource
  "Alana Gall; Kate Anderson; Kirsten Howard; Abbey Diaz; Alexandra King; Esther Willing; Michele Connolly; Daniel Lindsay; Gail Garvey"
  "Wellbeing of Indigenous Peoples in Canada, Aotearoa (New Zealand) and the United States: A Systematic Review"
  "International Journal of Environmental Research and Public Health 18(11), 5832"
  "2021"
  "10.3390/ijerph18115832"
  "https://doi.org/10.3390/ijerph18115832"
  Attr.academicArticleSource
  "systematic-review evidence on Indigenous wellbeing and self-determination; not an isolated land-return causal experiment"
  Attr.publicAttribution

gutierrezKaloostianRedvers2023Source : Attr.AttributedSource
gutierrezKaloostianRedvers2023Source = Attr.mkDOISource
  "Belinda V. Gutierrez; Damita Kaloostian; Nicole Redvers"
  "Elements of Successful Food Sovereignty Interventions within Indigenous Communities in the United States and Canada: a Systematic Review"
  "Current Developments in Nutrition 7(9), 101973"
  "2023"
  "10.1016/j.cdnut.2023.101973"
  "https://doi.org/10.1016/j.cdnut.2023.101973"
  Attr.academicArticleSource
  "systematic-review evidence on Indigenous food-sovereignty interventions"
  Attr.publicAttribution

vasco2018Source : Attr.AttributedSource
vasco2018Source = Attr.mkDOISource
  "Cristian Vasco; Richard Bilsborrow; Bolier Torres; Verena Griess"
  "Agricultural land use among mestizo colonist and indigenous populations: Contrasting patterns in the Amazon"
  "PLOS ONE 13(7), e0199518"
  "2018"
  "10.1371/journal.pone.0199518"
  "https://doi.org/10.1371/journal.pone.0199518"
  Attr.academicArticleSource
  "peer-reviewed comparative household-survey evidence; no causal interpretation is imported from metadata"
  Attr.publicAttribution

arcoiteJohnson2025Source : Attr.AttributedSource
arcoiteJohnson2025Source = Attr.mkDOISource
  "Brigitte Arcoite; Daniel K. N. Johnson"
  "Land-Back to Move Forward? The Measurable Relationship between Land-Back Movements and Economic Outcomes in Indigenous Communities within the U.S."
  "SSRN working paper 5189600"
  "2025"
  "10.2139/ssrn.5189600"
  "https://doi.org/10.2139/ssrn.5189600"
  Attr.academicArticleSource
  "working-paper causal-method claim; DOI metadata does not promote the paper to peer-reviewed status"
  Attr.publicAttribution

wri2016Source : Attr.AttributedSource
wri2016Source = Attr.mkNoDOISource
  "Helen Ding; Peter Veit; Erin Gray; Katie Reytar; Juan-Carlos Altamirano; Allen Blackman; Benjamin Hodgdon"
  "Climate Benefits, Tenure Costs: The Economic Case For Securing Indigenous Land Rights in the Amazon"
  "World Resources Institute report; ISBN 978-1-56973-894-8"
  "2016"
  "https://www.wri.org/research/climate-benefits-tenure-costs"
  Attr.institutionalSource
  "economic valuation and tenure-cost report; no DOI is recorded by this atlas and valuation does not equal realised market revenue"
  Attr.publicAttribution

cpi2024Source : Attr.AttributedSource
cpi2024Source = Attr.mkNoDOISource
  "João Mourão; Mariana Stussi; Priscila Souza"
  "Credit Where It's Due: Unearthing the Relationship between Rural Credit Subsidies and Deforestation"
  "Climate Policy Initiative / PUC-Rio policy research"
  "2024"
  "https://www.climatepolicyinitiative.org/publication/credit-where-its-due-unearthing-the-relationship-between-rural-credit-subsidies-and-deforestation/"
  Attr.institutionalSource
  "independent policy analysis using official underlying datasets; official data provenance does not transfer government authorship"
  Attr.publicAttribution

biaCarbon2023Source : Attr.AttributedSource
biaCarbon2023Source = Attr.mkNoDOISource
  "U.S. Department of the Interior, Bureau of Indian Affairs, Office of Trust Services"
  "NPM-TRUS-47 A1 Carbon Sequestration Agreement Policy - Amendment 1"
  "Bureau of Indian Affairs National Policy Memorandum"
  "2023"
  "https://www.bia.gov/sites/default/files/dup/assets/public/raca/national_policy_memoranda/pdf/npm-trus-47_a1_carbon_sequestration_policy_amendment_1_final_signed_10.31.23_w.footers_508.pdf"
  Attr.governmentSource
  "official administrative-policy classification; the agency's trust-asset category is not treated as an exhaustive ontology of ecological, cultural or stewardship value"
  Attr.publicAttribution

abatable2025Source : Attr.AttributedSource
abatable2025Source = Attr.mkNoDOISource
  "Abatable"
  "The new floor price for REDD+ carbon credits"
  "Abatable market commentary / market observation"
  "2025"
  "https://www.abatable.com/blog/the-new-floor-price-for-redd-carbon-credits"
  (Attr.namedSourceKind "commercial market observation")
  "commercial market-price observation; not legal authority or social-value estimate"
  Attr.publicAttribution

landBackAttributedSources : List Attr.AttributedSource
landBackAttributedSources =
  denBraber2024Source ∷ baragwanathBayi2020Source ∷ baragwanathBayiShinde2023Source ∷
  probst2020Source ∷ sze2022Source ∷ garnett2018Source ∷ mortonNinomiya2023Source ∷
  gall2021Source ∷ gutierrezKaloostianRedvers2023Source ∷ vasco2018Source ∷
  arcoiteJohnson2025Source ∷ wri2016Source ∷ cpi2024Source ∷ biaCarbon2023Source ∷
  abatable2025Source ∷ []

landBackAttributedSourceAtlas : Attr.AttributedSourceAtlas
landBackAttributedSourceAtlas = Attr.mkSourceAtlas
  "SensibLaw Indigenous LAND BACK / stewardship attributed-source atlas"
  "DASHI.Cognition.PNF.SensibLawIndigenousLandBackAttributedSourceAtlasExact"
  landBackAttributedSources
  "structured author/title/publication/year/DOI-or-atlas-local-no-DOI/URL/source-kind metadata for the current evidence lane; metadata identity is non-promoting"

atlasDoesNotCreateAuthority :
  Attr.atlasCreatesAuthority landBackAttributedSourceAtlas ≡ false
atlasDoesNotCreateAuthority = refl

noDoiClaimIsAtlasLocal :
  Attr.absentDOIClaimIsAtlasLocal landBackAttributedSourceAtlas ≡ true
noDoiClaimIsAtlasLocal = refl

wriHasNoDoiRecordedByThisAtlas :
  Attr.doiState wri2016Source ≡ Attr.noDOIRecordedByAtlas
wriHasNoDoiRecordedByThisAtlas = refl

arcoiteDoiDoesNotMeanPeerReview :
  Authority.publicationStatus Authority.arcoiteJohnson2025Authority
  ≡ Authority.workingPaperNotPeerReviewed
arcoiteDoiDoesNotMeanPeerReview = refl

data CitationMetadataCreatesSubstantiveAuthority : Set where
data NoDoiRecordedMeansNoDoiExistsAnywhere : Set where

metadataDoesNotCreateSubstantiveAuthority : CitationMetadataCreatesSubstantiveAuthority → ⊥
metadataDoesNotCreateSubstantiveAuthority ()

atlasLocalNoDoiDoesNotMakeUniversalAbsenceClaim : NoDoiRecordedMeansNoDoiExistsAnywhere → ⊥
atlasLocalNoDoiDoesNotMakeUniversalAbsenceClaim ()
