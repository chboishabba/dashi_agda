module DASHI.Law.SensibLawWoogarooS102TreeGISCompletionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogaroo9281NegotiatedApprovedGeometryExact as Geometry
import DASHI.Law.SensibLawWoogarooS102StatutorySpatialRelationExact as Statute

------------------------------------------------------------------------
-- S 102 TREE/GIS COMPLETION LANE
--
-- This owner starts only after the negotiated approved-plan carrier has been
-- acquired.  It separates plan-scale tree/clearing symbology from an exact
-- GIS-derived individual-tree or canopy product and from legal significance.
--
-- Statutory correction: exact/perfect spatial overlap is not the textual
-- threshold in NCA s 102. Spatial work is evidence for identifying the
-- threatening process, affected ecological object, causal/effect relation and
-- order land.  Section 103(2) expressly permits order land even where the
-- wildlife or habitat is not itself within that land.
------------------------------------------------------------------------

data TreeSpatialSourceKind : Set where
  approvedTreePlan : TreeSpatialSourceKind
  lidarPointCloud : TreeSpatialSourceKind
  aerialOrSatelliteImagery : TreeSpatialSourceKind
  stateHabitatPolygon : TreeSpatialSourceKind
  observerOccurrence : TreeSpatialSourceKind

record OpenTreeSpatialSource : Set where
  constructor open-tree-spatial-source
  field
    sourceKind : TreeSpatialSourceKind
    sourceName : String
    publicSurface : String
    spatialUse : String
    precisionBoundary : String

open OpenTreeSpatialSource public

approvedTreeInterface : OpenTreeSpatialSource
approvedTreeInterface = open-tree-spatial-source
  approvedTreePlan
  "A12705838 / 9281/2024/OW negotiated approved plans"
  "Council-stamped plan set supplied in the investigation corpus"
  "Anchor approved extent-of-work, bushfire-clearing, bushland-management and tree-retention/removal interfaces before external GIS overlay."
  "Plan symbols are not a complete inventory of every tree and are not yet a machine-precise GIS layer."

qldLidar : OpenTreeSpatialSource
qldLidar = open-tree-spatial-source
  lidarPointCloud
  "Queensland LiDAR / ELVIS"
  "Queensland open-data LiDAR coverage and ELVIS download/web-service route"
  "When acquired later, derive canopy height and candidate individual-tree crown/apex points where coverage and density are adequate; compare against approved clearing geometry and habitat structure."
  "LiDAR acquisition is deferred and is not a blocker for current Agda/legal work. A LiDAR-derived crown is a remote-sensing object, not automatically a botanical individual or protected tree."

qldImagery : OpenTreeSpatialSource
qldImagery = open-tree-spatial-source
  aerialOrSatelliteImagery
  "Queensland Globe / public imagery footprints / orthophoto sources"
  "Queensland Globe and Queensland imagery-footprint/open-data services"
  "Visually validate canopy continuity, roads, gullies and plan georeferencing; where imagery resolution permits, segment visible crowns."
  "Satellite imagery such as Sentinel-2 is useful for woody cover/change but is generally too coarse to enumerate every individual tree; high-resolution orthophoto availability must be checked separately."

slats : OpenTreeSpatialSource
slats = open-tree-spatial-source
  aerialOrSatelliteImagery
  "Statewide Landcover and Trees Study (SLATS) Sentinel-2 series"
  "Queensland Open Data"
  "Measure woody vegetation extent/change and provide an independent time-series check for clearing or regrowth."
  "This is a woody-cover/change product, not an individual-tree inventory."

qldKoalaHabitat : OpenTreeSpatialSource
qldKoalaHabitat = open-tree-spatial-source
  stateHabitatPolygon
  "Queensland Koala Plan / MSES habitat layers"
  "Queensland ArcGIS REST / Open Data"
  "Relate negotiated clearing/tree geometry to core and locally refined koala habitat polygons and related MSES surfaces."
  "Habitat polygons are model/regulatory surfaces and do not identify each tree or by themselves prove NCA s 13 essentiality or NCA s 102 satisfaction."

frogIDOccurrence : OpenTreeSpatialSource
frogIDOccurrence = open-tree-spatial-source
  observerOccurrence
  "FrogID captures 948283 and 948284"
  "Observer-supplied native FrogID coordinates near Opossum Creek"
  "Relate current occurrence coordinates to approved works, creek/corridor and habitat surfaces after georeferencing. Exact overlap may strengthen a factual causal account but is not a statutory s 102 prerequisite."
  "Pending/observer evidence remains distinct from expert-validated species occurrence and from any legal trigger."

------------------------------------------------------------------------
-- Completion state for the s 102 spatial lane.
------------------------------------------------------------------------

record S102SpatialCompletion : Set where
  constructor s102-spatial-completion
  field
    negotiatedPlanCarrierPaid : Bool
    planScaleClearingGeometryPaid : Bool
    planTreeInterfacePaid : Bool
    openLiDARRouteLocated : Bool
    openWoodyChangeRouteLocated : Bool
    openStateHabitatLayersLocated : Bool
    lidarAcquisitionDeferred : Bool
    exactLiDARCoverageChecked : Bool
    individualTreeCandidatesDerived : Bool
    planGeoreferenced : Bool
    exactClearingPolygonDigitised : Bool
    habitatSpatialRelationComputed : Bool
    frogIDSpatialRelationComputed : Bool
    perfectOverlapRequiredByStatute : Bool
    condition6aReceiptAcquired : Bool
    prestartReceiptAcquired : Bool
    commencementEvidenceAcquired : Bool

currentS102SpatialCompletion : S102SpatialCompletion
currentS102SpatialCompletion = s102-spatial-completion
  true true true true true true true
  false false false false false false false false false false

record S102NextCut : Set where
  constructor s102-next-cut
  field
    highestAlphaSpatialAction : String
    highestAlphaExecutionAction : String
    legalUse : String

open S102NextCut public

currentS102NextCut : S102NextCut
currentS102NextCut = s102-next-cut
  "Use A12705838 now to georeference/digitise the negotiated approved works and bushfire-clearing surfaces against roads, gullies, cadastral/habitat anchors and current occurrence points. Treat later LiDAR as an optional evidence-refinement path rather than a prerequisite."
  "Acquire the Condition 6(a) satisfaction evidence, prestart record and commencement/clearing chronology; these remain independent of spatial precision."
  "Feed spatial relations, process identity, habitat/species evidence and execution timing to the NCA ss 102-107 consumer. The legal question is whether a qualifying wildlife/habitat/area is subject to a threatening process likely to have significant detrimental effect, not whether every relevant point perfectly overlaps the approved clearing polygon."

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data CrownCandidateEqualsBotanicalTree : Set where
data SatellitePixelEqualsIndividualTree : Set where
data TreeCountEqualsHabitatFunction : Set where
data KoalaHabitatPolygonEqualsNCA13CriticalHabitat : Set where
data SpatialOverlapEqualsS102Order : Set where
data PerfectOverlapEqualsS102Element : Set where
data LackOfPerfectOverlapEqualsS102Unavailable : Set where
data ApprovedClearingEnvelopeEqualsCommencedClearing : Set where
data FrogIDPointEqualsValidatedLegalSpeciesFact : Set where

crownCandidateDoesNotBecomeBotanicalIdentity : CrownCandidateEqualsBotanicalTree → ⊥
crownCandidateDoesNotBecomeBotanicalIdentity ()

satellitePixelDoesNotBecomeTree : SatellitePixelEqualsIndividualTree → ⊥
satellitePixelDoesNotBecomeTree ()

treeCountDoesNotBecomeHabitatFunction : TreeCountEqualsHabitatFunction → ⊥
treeCountDoesNotBecomeHabitatFunction ()

koalaPolygonDoesNotBecomeNCA13 : KoalaHabitatPolygonEqualsNCA13CriticalHabitat → ⊥
koalaPolygonDoesNotBecomeNCA13 ()

spatialOverlapDoesNotCreateOrder : SpatialOverlapEqualsS102Order → ⊥
spatialOverlapDoesNotCreateOrder ()

perfectOverlapDoesNotBecomeElement : PerfectOverlapEqualsS102Element → ⊥
perfectOverlapDoesNotBecomeElement ()

noPerfectOverlapDoesNotForecloseRoute : LackOfPerfectOverlapEqualsS102Unavailable → ⊥
noPerfectOverlapDoesNotForecloseRoute ()

approvedEnvelopeDoesNotProveCommencement : ApprovedClearingEnvelopeEqualsCommencedClearing → ⊥
approvedEnvelopeDoesNotProveCommencement ()

frogIDPointDoesNotBecomeValidatedLegalFact : FrogIDPointEqualsValidatedLegalSpeciesFact → ⊥
frogIDPointDoesNotBecomeValidatedLegalFact ()
