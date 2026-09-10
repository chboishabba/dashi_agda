module DASHI.Law.SensibLawWoogarooLESCanopyLiDARSourceSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Law.SensibLawWoogarooLESCanopyLiDARInteropExact as Interop

------------------------------------------------------------------------
-- WOOGAROO × LES CANOPY/LIDAR SOURCE SNOWBALL
--
-- Attribution-first method lineage for a future LES worker.  This module does
-- not claim that every surrounding source implements the Woogaroo pipeline,
-- nor that a remembered media item has been uniquely identified.  It records
-- the strongest currently located UQ/LES-relevant sources and keeps project,
-- conference, researcher-profile and peer-reviewed article roles distinct.
------------------------------------------------------------------------

avilasProject : Source.AttributedSource
avilasProject = Source.mkNoDOISource
  "William Woodgate; Stuart Phinn"
  "AVILAS: Automating individual tree-scale vegetation structure and aboveground biomass inventory and monitoring at local to regional scales with drone LiDAR and satellite data"
  "University of Queensland Experts — Innovative Biodiversity Monitoring Program project"
  "2024-2026"
  "https://about.uq.edu.au/experts/project/63009"
  Source.institutionalSource
  "Primary UQ project receipt for automated individual-tree-scale vegetation structure/biomass inventory using drone LiDAR plus satellite data; candidate upstream method owner for later LES tree/crown extraction work."
  Source.publicAttribution

avilasAEOFPresentation : Source.AttributedSource
avilasAEOFPresentation = Source.mkNoDOISource
  "William Woodgate; Joshua Rivory; Stuart Phinn; Glen Eaton; Tim Devereux; Raja Aryal; Shaun Levick; Tom Lowe"
  "AVILAS — Automating individual tree-scale vegetation structure and aboveground biomass inventory and monitoring at local to regional scales with drone LiDAR and satellite data"
  "Australian Earth Observation Forum 2024 presentation"
  "2024"
  "https://static1.squarespace.com/static/664a91666f69542ebd2f6aff/t/6715f0facdcf0b18b4c23290/1729491208353/AEOF%2B2024%2BWilliam%2BWoodgate.pdf"
  (Source.namedSourceKind "conference presentation")
  "Public method-description carrier stating the AVILAS objective of automated low-level tree/branch metric extraction over large plots from high-resolution UAV LiDAR; useful for future LES implementation requirements, not a peer-reviewed validation result."
  Source.publicAttribution

rayExtractArticle : Source.AttributedSource
rayExtractArticle = Source.mkDOISource
  "Timothy Devereux; Thomas Lowe; Joshua Rivory; Rafael Bohn Reckziegel; Kim Calders; Raja Ram Aryal; Glen Eaton; Zane Cooper; Shaun Levick; Stuart Phinn; William Woodgate"
  "RayExtract: A fast, scalable method for tree volume reconstruction from terrestrial laser scanning"
  "Remote Sensing of Environment 334, 115162"
  "2026"
  "10.1016/j.rse.2025.115162"
  "https://doi.org/10.1016/j.rse.2025.115162"
  Source.academicArticleSource
  "Peer-reviewed UQ-linked method surrounding the AVILAS lane: automated plot/tree woody-volume reconstruction from terrestrial laser scanning with segmentation/reconstruction validation. Relevant to structural-tree reconstruction and calibration receipts, not proof that airborne/drone LiDAR can directly identify every Woogaroo tree or species."
  Source.publicAttribution

forestDigitalTwinArticle : Source.AttributedSource
forestDigitalTwinArticle = Source.mkDOISource
  "Chang Liu; Kim Calders; Niall Origo; Mathias Disney; Félicien Meunier; William Woodgate; Jean-Philippe Gastellu-Etchegorry; Joanne Nightingale; Eija Honkavaara; Teemu Hakala; Lauri Markelin; Hans Verbeeck"
  "Reconstructing the digital twin of forests from a 3D library: Quantifying trade-offs for radiative transfer modeling"
  "Remote Sensing of Environment 298, 113832"
  "2023"
  "10.1016/j.rse.2023.113832"
  "https://doi.org/10.1016/j.rse.2023.113832"
  Source.academicArticleSource
  "Peer-reviewed forest digital-twin and 3D reconstruction source with UQ co-authorship; supports the LES idea that explicit 3D forest structure can be reconstructed for EO calibration/validation while preserving sampling/reconstruction trade-offs."
  Source.publicAttribution

deVereuxUQProject : Source.AttributedSource
deVereuxUQProject = Source.mkNoDOISource
  "Tim Devereux"
  "Synthetic Reference Data to Improve Canopy Structure Retrievals from Multi-platform LiDAR"
  "University of Queensland School of the Environment researcher/project profile"
  "2023-2026"
  "https://environment.uq.edu.au/profile/26972/tim-devereux"
  Source.institutionalSource
  "UQ project-lineage receipt for terrestrial LiDAR, spectral measurements, high-fidelity digital twins and calibration/validation of LiDAR canopy-metric retrieval algorithms across platforms."
  Source.publicAttribution

lydiaLiUQCanopyWork : Source.AttributedSource
lydiaLiUQCanopyWork = Source.mkNoDOISource
  "Lydia Li"
  "UQ research program: canopy height modelling by integrating GEDI LiDAR and Sentinel-2 satellite data"
  "University of Queensland School of the Environment researcher profile"
  "2026"
  "https://environment.uq.edu.au/profile/29926/lydia-li"
  Source.institutionalSource
  "Current UQ research-program receipt for scalable canopy-height estimation using GEDI LiDAR, Sentinel-2, HPC/cloud and machine learning; useful surrounding method lineage for LES canopy-height products. No specific peer-reviewed article is attributed by this profile alone."
  Source.publicAttribution

nonUQCanopyHeightArticle : Source.AttributedSource
nonUQCanopyHeightArticle = Source.mkDOISource
  "Hormoz Sohrabi; Laya Zeinali Yadegari; Elia Quirós; Markus Immitzer"
  "Canopy height mapping in complex temperate forests using spaceborne GEDI LiDAR and multitemporal Sentinel-2 data"
  "Smart Agricultural Technology 14, 102249"
  "2026"
  "10.1016/j.atech.2026.102249"
  "https://doi.org/10.1016/j.atech.2026.102249"
  Source.academicArticleSource
  "Recent open peer-reviewed surrounding source for GEDI + multitemporal Sentinel-2 canopy-height mapping, local calibration and spatial-alignment error. Included specifically as a non-UQ comparison source: it must not be attributed to UQ merely because its method resembles current UQ work."
  Source.publicAttribution

uqCanopyLiDARAtlas : Source.AttributedSourceAtlas
uqCanopyLiDARAtlas = Source.mkSourceAtlas
  "Woogaroo LES canopy/LiDAR source snowball"
  "DASHI.Law.SensibLawWoogarooLESCanopyLiDARSourceSnowballExact"
  (avilasProject ∷
   avilasAEOFPresentation ∷
   rayExtractArticle ∷
   forestDigitalTwinArticle ∷
   deVereuxUQProject ∷
   lydiaLiUQCanopyWork ∷
   nonUQCanopyHeightArticle ∷
   [])
  "Attribution-first lineage for future LES implementation of canopy/tree structure, calibration and GIS evidence packets; project descriptions, profiles and articles remain distinct source roles."

------------------------------------------------------------------------
-- Snowball handoff for the next LES worker.
------------------------------------------------------------------------

data SourceRole : Set where
  uqProjectOwner : SourceRole
  publicMethodPresentation : SourceRole
  peerReviewedTreeReconstruction : SourceRole
  peerReviewedForestDigitalTwin : SourceRole
  uqCalibrationProgram : SourceRole
  uqCanopyHeightProgram : SourceRole
  externalComparator : SourceRole

record LESSourceSnowballEdge : Set where
  constructor les-source-snowball-edge
  field
    role : SourceRole
    source : Source.AttributedSource
    implementationQuestion : String
    evidenceBoundary : String

open LESSourceSnowballEdge public

avilasImplementationEdge : LESSourceSnowballEdge
avilasImplementationEdge = les-source-snowball-edge
  uqProjectOwner
  avilasProject
  "How should LES ingest high-resolution LiDAR plus satellite context and emit provenance-bearing individual-tree-scale structural candidates at local-to-regional scale?"
  "Project aim is not an implemented Woogaroo algorithm and does not certify a particular segmentation accuracy."

rayExtractImplementationEdge : LESSourceSnowballEdge
rayExtractImplementationEdge = les-source-snowball-edge
  peerReviewedTreeReconstruction
  rayExtractArticle
  "Which reconstruction/segmentation invariants and validation receipts should LES preserve when converting point clouds into explicit woody-tree structure?"
  "TLS woody-volume reconstruction is not identical to aerial crown detection; transfer requires a separately typed adapter and calibration."

digitalTwinImplementationEdge : LESSourceSnowballEdge
forestDigitalTwinImplementationEdge = les-source-snowball-edge
  peerReviewedForestDigitalTwin
  forestDigitalTwinArticle
  "How should LES represent explicit forest 3D structure and document reconstruction/sampling trade-offs when calibrating EO products?"
  "A synthetic/digital forest reconstruction remains a model of structure, not an observed inventory unless same-object acquisition and validation are attached."

canopyHeightImplementationEdge : LESSourceSnowballEdge
canopyHeightImplementationEdge = les-source-snowball-edge
  uqCanopyHeightProgram
  lydiaLiUQCanopyWork
  "How should LES fuse sparse LiDAR vertical-structure measurements with wall-to-wall optical data while retaining local calibration, geolocation and uncertainty as first-class receipts?"
  "Research-program description is not a paper-level quantitative performance claim."

comparisonImplementationEdge : LESSourceSnowballEdge
comparisonImplementationEdge = les-source-snowball-edge
  externalComparator
  nonUQCanopyHeightArticle
  "Use the published GEDI/Sentinel-2 workflow as an external comparator for canopy-height fusion, spatial-alignment correction and dense-canopy saturation failure modes."
  "This source is not UQ-authored and must not be used to attribute its results to the UQ AVILAS/Lydia Li programs."

------------------------------------------------------------------------
-- Remembered-paper identity stays unresolved rather than being manufactured.
------------------------------------------------------------------------

record RememberedPaperIdentityState : Set where
  constructor remembered-paper-identity-state
  field
    exactRememberedMediaPaperIdentified : Bool
    strongestUQMethodMatch : String
    strongestRecentUQPeerReviewedNeighbour : String
    strongestRecentNonUQMethodMatch : String
    residual : String

rememberedPaperIdentityState : RememberedPaperIdentityState
rememberedPaperIdentityState = remembered-paper-identity-state
  false
  "AVILAS (2024-2026): automated individual-tree-scale vegetation structure/biomass with drone LiDAR + satellite data"
  "RayExtract (Remote Sensing of Environment, 2026; DOI 10.1016/j.rse.2025.115162)"
  "Canopy height mapping in complex temperate forests using GEDI LiDAR and multitemporal Sentinel-2 (2026; DOI 10.1016/j.atech.2026.102249)"
  "Do not collapse the user's remembered 'recent UQ canopy/LiDAR paper' to one of these without a unique source match; the surrounding method lineage is already sufficient for an LES worker to proceed."

------------------------------------------------------------------------
-- Attribution firewalls.
------------------------------------------------------------------------

data UQProjectEqualsPeerReviewedValidation : Set where
data ResearcherProfileEqualsArticle : Set where
data MethodSimilarityEqualsCommonAuthorship : Set where
data SurroundingSourceEqualsWoogarooResult : Set where
data CitationEqualsLESImplementation : Set where

uqProjectDoesNotBecomePeerReviewedValidation : UQProjectEqualsPeerReviewedValidation → ⊥
uqProjectDoesNotBecomePeerReviewedValidation ()

profileDoesNotBecomeArticle : ResearcherProfileEqualsArticle → ⊥
profileDoesNotBecomeArticle ()

methodSimilarityDoesNotCreateAuthorship : MethodSimilarityEqualsCommonAuthorship → ⊥
methodSimilarityDoesNotCreateAuthorship ()

sourceDoesNotCreateWoogarooResult : SurroundingSourceEqualsWoogarooResult → ⊥
sourceDoesNotCreateWoogarooResult ()

citationDoesNotImplementLES : CitationEqualsLESImplementation → ⊥
citationDoesNotImplementLES ()
