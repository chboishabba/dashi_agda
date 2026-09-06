module DASHI.Cognition.PNF.SensibLawIndigenousLandBackAttributedSourceAtlasSupplementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.AttributedSourceCore as Attr

------------------------------------------------------------------------
-- Supplementary structured metadata for policy/history/administrative sources
-- already used elsewhere in the LAND BACK lane.
------------------------------------------------------------------------

binswanger1991Source : Attr.AttributedSource
binswanger1991Source = Attr.mkDOISource
  "Hans P. Binswanger"
  "Brazilian policies that encourage deforestation in the Amazon"
  "World Development 19(7), 821-829"
  "1991"
  "10.1016/0305-750X(91)90135-5"
  "https://doi.org/10.1016/0305-750X(91)90135-5"
  Attr.academicArticleSource
  "historical peer-reviewed analysis of tax, land-allocation and agricultural-credit incentives; historical scope must remain explicit"
  Attr.publicAttribution

margulis2003Source : Attr.AttributedSource
margulis2003Source = Attr.mkNoDOISource
  "Sergio Margulis"
  "Causes of Deforestation of the Brazilian Amazon"
  "World Bank Working Paper No. 22 / Report No. 27715; ISBN 0-8213-5691-7"
  "2003"
  "https://documents.worldbank.org/en/publication/documents-reports/documentdetail/758171468768828889"
  Attr.institutionalSource
  "World Bank analytical report; private profitability, social cost and policy-mechanism claims retain report authorship and historical/contextual scope"
  Attr.publicAttribution

ashDatabook2025Source : Attr.AttributedSource
ashDatabook2025Source = Attr.mkNoDOISource
  "Randall Akee; Elijah Moreno; Amy Besaw Medford"
  "Social and Economic Changes in American Indian Reservations: A Databook of the US Census and the American Community Survey, Third Edition, 1990-2020"
  "Harvard Kennedy School Project on Indigenous Governance and Development / Ash Center"
  "2025"
  "https://ash.harvard.edu/resources/social-and-economic-changes-in-american-indian-reservations-a-databook-of-the-us-census-and-the-american-community-survey-third-edition/"
  Attr.academicBookSource
  "academic descriptive statistical synthesis of public-use Census/ACS data; underlying government data do not make the derived analysis an official administrative receipt"
  Attr.publicAttribution

interiorLandBuyBack2023Source : Attr.AttributedSource
interiorLandBuyBack2023Source = Attr.mkNoDOISource
  "U.S. Department of the Interior"
  "Ten Years of Consolidating Land and Building Trust / Land Buy-Back Program for Tribal Nations program conclusion"
  "U.S. Department of the Interior administrative program reporting"
  "2023"
  "https://www.bia.gov/bia/history/history-indian-land-consolidation"
  Attr.governmentSource
  "official administrative receipt for program design and land-consolidation totals; program totals do not by themselves identify causal socioeconomic effects"
  Attr.publicAttribution

embrapaPoyanawa2021Source : Attr.AttributedSource
embrapaPoyanawa2021Source = Attr.mkNoDOISource
  "Embrapa"
  "Study reveals Indigenous Land's potential to generate carbon credits"
  "Embrapa research communication on Poyanawa Indigenous Land"
  "2021"
  "https://www.embrapa.br/en/busca-de-noticias/-/noticia/63600123/study-reveals-indigenous-lands-potential-to-generate-carbon-credits"
  Attr.governmentSource
  "government research communication summarising a Poyanawa avoided-deforestation/carbon-credit study; communication-level estimates are not promoted into a universal causal theorem"
  Attr.publicAttribution

supplementaryAttributedSources : List Attr.AttributedSource
supplementaryAttributedSources =
  binswanger1991Source ∷ margulis2003Source ∷ ashDatabook2025Source ∷
  interiorLandBuyBack2023Source ∷ embrapaPoyanawa2021Source ∷ []

supplementarySourceAtlas : Attr.AttributedSourceAtlas
supplementarySourceAtlas = Attr.mkSourceAtlas
  "SensibLaw LAND BACK policy/history attributed-source supplement"
  "DASHI.Cognition.PNF.SensibLawIndigenousLandBackAttributedSourceAtlasSupplementExact"
  supplementaryAttributedSources
  "structured metadata supplement for historical-policy, academic descriptive, government administrative and government research-communication sources"

supplementDoesNotCreateAuthority :
  Attr.atlasCreatesAuthority supplementarySourceAtlas ≡ false
supplementDoesNotCreateAuthority = refl

supplementNoDoiClaimsAreAtlasLocal :
  Attr.absentDOIClaimIsAtlasLocal supplementarySourceAtlas ≡ true
supplementNoDoiClaimsAreAtlasLocal = refl
