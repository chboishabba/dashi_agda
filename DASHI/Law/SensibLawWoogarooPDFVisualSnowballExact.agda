module DASHI.Law.SensibLawWoogarooPDFVisualSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import DASHI.Law.SensibLawWoogarooPDFSnowballCorpusExact

------------------------------------------------------------------------
-- VISUAL PAGE SNOWBALL
--
-- PDF text extraction and rendered page imagery are separate evidence
-- channels.  Maps, aerials, survey-point figures, tables and image-dominant
-- Development.i extracts must be inspected as pages rather than inferred
-- from parser output alone.
------------------------------------------------------------------------

data VisualKind : Set where
  sitePlan : VisualKind
  habitatMap : VisualKind
  surveyMap : VisualKind
  historicalAerial : VisualKind
  surroundingDevelopmentMap : VisualKind
  developmentApprovalScreenshot : VisualKind
  tableOrDiagram : VisualKind
  otherVisual : VisualKind

data VisualStatus : Set where
  notYetReviewed : VisualStatus
  pageReviewed : VisualStatus
  spatialLeadRecorded : VisualStatus
  exactGeometryStillOpen : VisualStatus

record VisualSnowballReceipt : Set where
  constructor visual-snowball-receipt
  field
    carrierLabel : String
    project : SnowballProject
    pageReference : String
    visualKind : VisualKind
    observedVisual : String
    attribution : String
    status : VisualStatus
    residual : String

open VisualSnowballReceipt public

bellevueKoalaMappingVisual : VisualSnowballReceipt
bellevueKoalaMappingVisual = visual-snowball-receipt
  "2018-8350 Attachment 10 - Queensland Koala Mapping"
  epbc20188350
  "rendered page 1; map requested 22 November 2018; Lot 901 RP909175"
  habitatMap
  "The page supplies a mapped parcel outline and Queensland koala-planning symbology around the Bellevue/Eugene Street site."
  "State of Queensland map reproduced in the proponent attachment"
  pageReviewed
  "Map-era categories must not be silently translated into current koala-map categories or another project's parcel facts."

bellevueSATVisual : VisualSnowballReceipt
bellevueSATVisual = visual-snowball-receipt
  "2018-8350 Attachment 16 - SAT Survey Locations"
  epbc20188350
  "rendered page 1"
  surveyMap
  "The aerial map spatially plots SAT survey areas, watercourses, transects and 2018 koala-evidence symbols inside the site boundary."
  "28 South Environmental"
  spatialLeadRecorded
  "Visual clustering is a spatial observation; ecological significance remains paid by the survey text/methodology and exact coordinates where available."

bellevueHistoricalAerialVisual : VisualSnowballReceipt
bellevueHistoricalAerialVisual = visual-snowball-receipt
  "2018-8350 Attachment 6a - Historical Analysis Figures"
  epbc20188350
  "rendered pages 1-3: 1955, 1968, 1974, 1978, 1982, 1987"
  historicalAerial
  "The same red site boundary and waterway/cadastre context are shown over six historical aerial epochs, allowing direct visual comparison of long-lived wooded cover and drainage geometry."
  "28 South Environmental historical-aerial figures"
  pageReviewed
  "Persistence of visible tree cover does not by itself determine stand age, remnant legal status, hollow density or habitat quality."

bellevueSurroundingReferralsVisual : VisualSnowballReceipt
bellevueSurroundingReferralsVisual = visual-snowball-receipt
  "2018-8350 Attachment 22 - EPBC Referrals in the Surrounding Locality"
  epbc20188350
  "rendered page 1"
  surroundingDevelopmentMap
  "The map places the Eugene Street site in a road/waterway/cadastral landscape with multiple coloured surrounding EPBC referral polygons, including Springview Village One."
  "28 South Environmental; source legend cites EPBC Referral Portal 2018 and State spatial datasets"
  spatialLeadRecorded
  "Adjacency and co-display do not merge referral identities or prove cumulative legal effect."

scenicConceptVisual : VisualSnowballReceipt
scenicConceptVisual = visual-snowball-receipt
  "2020-8651 7399 E 01 Concept Precinct Layout A"
  epbc20208651
  "rendered page 1"
  sitePlan
  "The aerial plan visually distinguishes the 36.12 ha Scenic Precinct, a 24.2 ha development footprint and an 11.92 ha Linear Park."
  "Saunders Havill Group for Springfield City Group"
  spatialLeadRecorded
  "The drawing is labelled preliminary/desktop and is not an approved survey plan unless a later approval adopts it."

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ParsedTextAutomaticallyPaysVisualContent : Set where

data VisualSimilarityProvesSameParcel : Set where

data ManualOverlayProvesGISIntersection : Set where

data HistoricalTreeCoverProvesStandAge : Set where

data DeveloperMapIsAgencyFinding : Set where

data CampaignAnnotationIsOfficialGeometry : Set where

noTextVisualCollapse : ParsedTextAutomaticallyPaysVisualContent → ⊥
noTextVisualCollapse ()

noSimilarityIdentityCollapse : VisualSimilarityProvesSameParcel → ⊥
noSimilarityIdentityCollapse ()

noManualGISPromotion : ManualOverlayProvesGISIntersection → ⊥
noManualGISPromotion ()

noAerialAgePromotion : HistoricalTreeCoverProvesStandAge → ⊥
noAerialAgePromotion ()

noDeveloperAgencyPromotion : DeveloperMapIsAgencyFinding → ⊥
noDeveloperAgencyPromotion ()

noCampaignGeometryPromotion : CampaignAnnotationIsOfficialGeometry → ⊥
noCampaignGeometryPromotion ()

record VisualSnowballPolicy : Set where
  constructor visual-snowball-policy
  field
    inspectRenderedPages : Bool
    preservePageReference : Bool
    preserveVisualAttribution : Bool
    separateTextAndVisualClaims : Bool
    treatMapsAsAcquisitionEdges : Bool
    requireExactGISForIntersection : Bool

canonicalVisualSnowballPolicy : VisualSnowballPolicy
canonicalVisualSnowballPolicy = visual-snowball-policy
  true true true true true true
