module DASHI.Cognition.PNF.SensibLawCountryRelationalIrreversibilitySourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- SOURCE ATLAS
--
-- This atlas records source identity only.  Legal holding, treaty-body view,
-- inquiry finding, declaration text, critical interpretation and DASHI theorem
-- remain different proposition kinds downstream.
------------------------------------------------------------------------

highCourtGriffiths2019 : Source.AttributedSource
highCourtGriffiths2019 = Source.mkNoDOISource
  "High Court of Australia"
  "Northern Territory v Griffiths (deceased) and Jones on behalf of the Ngaliwurru and Nungali Peoples [2019] HCA 7"
  "High Court of Australia"
  "2019"
  "https://www.hcourt.gov.au/cases-and-judgments/judgments/judgments-1998-current/northern-territory-v-mr-griffiths-deceased-and-lorraine-jones-behalf-ngaliwurru-and-nungali-peoples"
  (Source.namedSourceKind "primary judicial decision")
  "primary judicial authority for native-title compensation/cultural-loss reasoning; especially [180]-[206], [230] on spiritual connection, responsibility to care for Country, incremental/cumulative effect and permanent/intergenerational loss"
  Source.publicAttribution

bringingThemHome1997 : Source.AttributedSource
bringingThemHome1997 = Source.mkNoDOISource
  "Human Rights and Equal Opportunity Commission"
  "Bringing them Home: Report of the National Inquiry into the Separation of Aboriginal and Torres Strait Islander Children from Their Families"
  "Commonwealth human-rights inquiry report"
  "1997"
  "https://humanrights.gov.au/bringing-them-home/the-report/bringing-them-home-report.html"
  Source.institutionalSource
  "institutional inquiry findings on forcible removal, destruction of cultural links, intergenerational effects, land/native-title consequences, restitution and genocide; not a judicial holding"
  Source.publicAttribution

undrip2007 : Source.AttributedSource
undrip2007 = Source.mkNoDOISource
  "United Nations General Assembly"
  "United Nations Declaration on the Rights of Indigenous Peoples"
  "General Assembly resolution 61/295"
  "2007"
  "https://www.un.org/development/desa/indigenouspeoples/wp-content/uploads/sites/19/2019/01/UNDRIP_E_web.pdf"
  (Source.namedSourceKind "international declaration")
  "international declaration; especially arts 8, 25, 26, 28 and 31 concerning culture, lands, spiritual relationship, future-generation responsibilities, redress and traditional knowledge"
  Source.publicAttribution

billyHRC2022 : Source.AttributedSource
billyHRC2022 = Source.mkNoDOISource
  "United Nations Human Rights Committee"
  "Billy and others v Australia, CCPR/C/135/D/3624/2019"
  "Views under article 5(4) of the First Optional Protocol to the ICCPR"
  "2022"
  "https://juris.ohchr.org/casedetails/3855/en-US"
  (Source.namedSourceKind "UN treaty-body views")
  "treaty-body merits/remedy authority for ICCPR arts 17 and 27 violations and effective-remedy/full-reparation requirements; not an Australian court judgment"
  Source.publicAttribution

pabai2025 : Source.AttributedSource
pabai2025 = Source.mkNoDOISource
  "Federal Court of Australia"
  "Pabai Pabai & Anor v Commonwealth of Australia (No 2) [2025] FCA 796"
  "Federal Court of Australia"
  "2025"
  "https://www.fedcourt.gov.au/services/access-to-files-and-transcripts/online-files/pabai-v-australia"
  (Source.namedSourceKind "primary judicial decision")
  "negative calibration for the pleaded Commonwealth climate-negligence route; does not definitionally foreclose every reformulated duty route"
  Source.publicAttribution

bartlettMarshallMarshall2012 : Source.AttributedSource
bartlettMarshallMarshall2012 = Source.mkDOISource
  "Cheryl Bartlett; Murdena Marshall; Albert Marshall"
  "Two-Eyed Seeing and other lessons learned within a co-learning journey of bringing together indigenous and mainstream knowledges and ways of knowing"
  "Journal of Environmental Studies and Sciences 2:331-340"
  "2012"
  "10.1007/s13412-012-0086-8"
  "https://doi.org/10.1007/s13412-012-0086-8"
  Source.academicArticleSource
  "source calibration for coordinated use of strengths from distinct knowledge systems without epistemic fusion; does not own DASHI factorisation theorems"
  Source.publicAttribution

patternMindSandTalk2019 : Source.AttributedSource
patternMindSandTalk2019 = Source.mkNoDOISource
  "Tyson Yunkaporta"
  "Sand Talk: How Indigenous Thinking Can Save the World"
  "Text Publishing"
  "2019"
  "https://www.textpublishing.com.au/books/sand-talk"
  Source.academicBookSource
  "historical entry point for repo-local PatternMind comparison vocabulary; not a universal Indigenous ontology and not authority for every Indigenous community"
  Source.publicAttribution

kimmerer2013 : Source.AttributedSource
kimmerer2013 = Source.mkNoDOISource
  "Robin Wall Kimmerer"
  "Braiding Sweetgrass: Indigenous Wisdom, Scientific Knowledge, and the Teachings of Plants"
  "Milkweed Editions"
  "2013"
  "https://milkweed.org/book/braiding-sweetgrass"
  Source.academicBookSource
  "source-bounded relational/reciprocity and braided-knowledge interpretation; does not own Australian Indigenous law, Country, or DASHI formal theorems"
  Source.publicAttribution

countryRelationalIrreversibilityAtlas : Source.AttributedSourceAtlas
countryRelationalIrreversibilityAtlas = Source.mkSourceAtlas
  "Country relational irreversibility / custodianship source atlas"
  "DASHI.Cognition.PNF.SensibLawCountryRelationalIrreversibilitySourceAtlasExact"
  (highCourtGriffiths2019
    ∷ bringingThemHome1997
    ∷ undrip2007
    ∷ billyHRC2022
    ∷ pabai2025
    ∷ bartlettMarshallMarshall2012
    ∷ patternMindSandTalk2019
    ∷ kimmerer2013
    ∷ [])
  "source identity for Country relation, transmission, cultural loss, custodial responsibility, remedy and plural-epistemic comparison; metadata does not create substantive truth, cultural authority or legal authority"

atlasDoesNotCreateAuthority :
  Source.atlasCreatesAuthority countryRelationalIrreversibilityAtlas ≡ false
atlasDoesNotCreateAuthority = refl
