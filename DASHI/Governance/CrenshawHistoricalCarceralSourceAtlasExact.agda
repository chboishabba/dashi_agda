module DASHI.Governance.CrenshawHistoricalCarceralSourceAtlasExact where

-- Source-attributed conceptual bridge. No source imports its thesis as an
-- Agda axiom, and no citation establishes a case-specific causal pathway.
-- Individual Black women, legal professionals, litigants and researchers
-- remain separate agents; we do not attribute unreported experiences.

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Attr

crenshaw1988 : Attr.AttributedSource
crenshaw1988 = Attr.mkDOISource
  "Kimberle Williams Crenshaw"
  "Race, Reform, and Retrenchment: Transformation and Legitimation in Antidiscrimination Law"
  "Harvard Law Review 101(7), 1331-1387"
  "1988"
  "10.2307/1341398"
  "https://scholarship.law.columbia.edu/faculty_scholarship/2866/"
  Attr.academicArticleSource
  "Crenshaw's rights/legitimation/material-subordination argument motivates a DASHI finite non-entailment example"
  Attr.publicAttribution

crenshaw1991 : Attr.AttributedSource
crenshaw1991 = Attr.mkDOISource
  "Kimberle Williams Crenshaw"
  "Mapping the Margins: Intersectionality, Identity Politics, and Violence Against Women of Color"
  "Stanford Law Review 43(6), 1241-1299"
  "1991"
  "10.2307/1229039"
  "https://web.usca.edu/media/usca/departments/institutional-culture-amp-belonging/Crenshaw-MappingMarginsIntersectionality-1991.pdf"
  Attr.academicArticleSource
  "Situated structural/political/representational intersectionality; no presumption that documented barriers measure fatigue"
  Attr.publicAttribution

blackGirlsMatter2015 : Attr.AttributedSource
blackGirlsMatter2015 = Attr.mkNoDOISource
  "Kimberle Williams Crenshaw, Priscilla Ocen and Jyoti Nanda"
  "Black Girls Matter: Pushed Out, Overpoliced and Underprotected"
  "African American Policy Forum and Center for Intersectionality and Social Policy Studies"
  "2015"
  "https://scholarship.law.columbia.edu/faculty_scholarship/3227/"
  Attr.academicArticleSource
  "Coauthored school-discipline and school-to-prison institutional evidence; youth and stakeholder participation must be acknowledged"
  Attr.publicAttribution

sayHerName2015 : Attr.AttributedSource
sayHerName2015 = Attr.mkNoDOISource
  "Kimberle Williams Crenshaw, Andrea J Ritchie, Rachel Anspach, Rachel Gilmer and Luke Harris"
  "Say Her Name: Resisting Police Brutality Against Black Women"
  "African American Policy Forum and Center for Intersectionality and Social Policy Studies"
  "2015"
  "https://scholarship.law.columbia.edu/faculty_scholarship/3226/"
  Attr.academicArticleSource
  "Coauthored police-violence documentation, explicitly non-exhaustive; does not make an evidence-gap into evidence of no violence"
  Attr.publicAttribution

historicalInstitutionalSourceAtlas : Attr.AttributedSourceAtlas
historicalInstitutionalSourceAtlas = Attr.mkSourceAtlas
  "Crenshaw historical, institutional and carceral cross-publication atlas"
  "DASHI Governance"
  (crenshaw1988 ∷ crenshaw1991 ∷ blackGirlsMatter2015
    ∷ sayHerName2015 ∷ [])
  "Bibliographic source provenance only: legislation, court opinion, archival history, school record and policing practice require independent claim-specific receipts"

sourceCountIsFour :
  Attr.sourceCount
    (Attr.sources historicalInstitutionalSourceAtlas)
    ≡ 4
sourceCountIsFour = refl

historicalCitationDoesNotCreateAuthority :
  Attr.atlasCreatesAuthority historicalInstitutionalSourceAtlas ≡ false
historicalCitationDoesNotCreateAuthority = refl

-- Preserve *two independently owned displays* without rewriting the PDF.
-- Columbia's faculty repository indexes all three scholar contributors.
blackGirlsMatterCatalogContributorIndex :
  Attr.sourceAuthor blackGirlsMatter2015 ≡
    "Kimberle Williams Crenshaw, Priscilla Ocen and Jyoti Nanda"
blackGirlsMatterCatalogContributorIndex = refl

-- The publisher PDF's original byline makes the lead/with credit explicit.
blackGirlsMatterOriginalPrintedByline : String
blackGirlsMatterOriginalPrintedByline =
  "By Kimberle Williams Crenshaw / with Priscilla Ocen and Jyoti Nanda"

blackGirlsMatterPrintedCreditPreserved :
  blackGirlsMatterOriginalPrintedByline ≡
  "By Kimberle Williams Crenshaw / with Priscilla Ocen and Jyoti Nanda"
blackGirlsMatterPrintedCreditPreserved = refl

-- The reports must not be reduced to their most visible scholarly author;
-- communities, interview participants and stakeholders contribute testimony,
-- not automatically the role of report coauthor or a reusable public identity.
