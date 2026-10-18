module DASHI.Geo.EarthEmbeddingAttributedSourcesExact where

open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
import DASHI.Core.AttributedSourceCore as Attribution

-- Source identity, scientific claim, and DASHI mathematical result remain
-- separate. Source identity is *not* evidence of truth, semantic equivalence
-- or an imported theorem. Use the repo-native attributable source constructors.

alphaEarthPaper : Attribution.AttributedSource
alphaEarthPaper = Attribution.mkNoDOISource
  "Brown et al."
  "AlphaEarth Foundations: An embedding field model for accurate and efficient global mapping from sparse label data"
  "arXiv:2507.22291"
  "2025"
  "https://arxiv.org/abs/2507.22291"
  Attribution.academicArticleSource
  "Original source of model-design and embedding-field claims; no proof is imported."
  Attribution.publicAttribution

alphaEarthDocumentation : Attribution.AttributedSource
alphaEarthDocumentation = Attribution.mkNoDOISource
  "Google Earth Engine / Google DeepMind"
  "Satellite Embedding V1 annual dataset and AlphaEarth COG dequantisation documentation"
  "Google for Developers"
  "2025-2026"
  "https://developers.google.com/earth-engine/guides/aef_on_gcs_readme"
  Attribution.institutionalSource
  "Public dataset encoding/dequantisation source; not proof of downstream accuracy."
  Attribution.publicAttribution

tesseraOriginal : Attribution.AttributedSource
tesseraOriginal = Attribution.mkNoDOISource
  "Feng et al."
  "TESSERA: Temporal Embeddings of Surface Spectra for Earth Representation and Analysis"
  "arXiv:2506.20380"
  "2025"
  "https://arxiv.org/abs/2506.20380"
  Attribution.academicArticleSource
  "Original authors' temporal training and representation claims."
  Attribution.publicAttribution

tesseraV2 : Attribution.AttributedSource
tesseraV2 = Attribution.mkNoDOISource
  "Feng et al."
  "TESSERA v2: Scaling Pixel-wise Earth Foundation Models"
  "arXiv:2607.03949, revision v2 August 2026"
  "2026"
  "https://arxiv.org/abs/2607.03949"
  Attribution.academicArticleSource
  "Authors' Matryoshka performance claims are benchmark measurements, not formal bounds."
  Attribution.publicAttribution

rahmanPhysical : Attribution.AttributedSource
rahmanPhysical = Attribution.mkNoDOISource
  "Mashrekur Rahman"
  "Physically Interpretable AlphaEarth Foundation Model Embeddings Enable LLM-Based Land Surface Intelligence"
  "arXiv:2602.10354"
  "2026"
  "https://arxiv.org/abs/2602.10354"
  Attribution.academicArticleSource
  "Original author's 12.1m CONUS sample and physical reconstruction findings, not Queensland validation."
  Attribution.publicAttribution

rahmanGeometry : Attribution.AttributedSource
rahmanGeometry = Attribution.mkNoDOISource
  "Mashrekur Rahman et al."
  "Characterizing AlphaEarth Embedding Geometry for Agentic Environmental Reasoning"
  "arXiv:2604.18715"
  "2026"
  "https://arxiv.org/abs/2604.18715"
  Attribution.academicArticleSource
  "Original authors' spectral and local geometry diagnostics, not a globally proved smooth manifold."
  Attribution.publicAttribution

ouZheng : Attribution.AttributedSource
ouZheng = Attribution.mkDOISource
  "Zhigang Ou and Yi Zheng"
  "Foundation-Scale Satellite Embeddings Reframe Hydrological Generalization as a Representation Problem"
  "Geophysical Research Letters 53 e2025GL121604"
  "2026"
  "10.1029/2025GL121604"
  "https://doi.org/10.1029/2025GL121604"
  Attribution.academicArticleSource
  "Authors' Australian 455-catchment results; Woogaroo is not a measured catchment in this ledger."
  Attribution.publicAttribution

geoTesseraSoftware : Attribution.AttributedSource
geoTesseraSoftware = Attribution.mkNoDOISource
  "University of Cambridge Earth Observation Group"
  "GeoTessera Python library, data coverage and Zarr interface"
  "Source repository and documentation"
  "2026"
  "https://github.com/ucam-eo/geotessera"
  Attribution.institutionalSource
  "Source of current access API and available v1.1/v2 provisioning, not a claim of coverage."
  Attribution.publicAttribution

woogarooCouncil : Attribution.AttributedSource
woogarooCouncil = Attribution.mkNoDOISource
  "Ipswich City Council"
  "Brisbane River Catchment — Woogaroo Creek"
  "Ipswich City Council catchment overview"
  "2026 (accessed)"
  "https://www.ipswich.qld.gov.au/About-Council/Initiatives/Environment/Waterways/Catchments-and-Plans/Brisbane-River-Catchment"
  Attribution.governmentSource
  "Documents 69 square kilometre Woogaroo/Mountain/Opossum catchment, not hydrodynamic proof."
  Attribution.publicAttribution

springfieldEmergencyPlan : Attribution.AttributedSource
springfieldEmergencyPlan = Attribution.mkNoDOISource
  "Queensland Government"
  "Springfield Lakes Main Lakes Emergency Action Plan"
  "Queensland dam safety/public emergency action plan, catchment description"
  "2024"
  "https://www.rdmw.qld.gov.au/__data/assets/pdf_file/0007/1619773/springfield-high-eap.pdf"
  Attribution.governmentSource
  "Source for Main Lakes discharge into Opossum Creek then Woogaroo Creek and Brisbane River."
  Attribution.publicAttribution

springfieldNatureCare : Attribution.AttributedSource
springfieldNatureCare = Attribution.mkNoDOISource
  "Springfield Lakes Nature Care"
  "The natural landscapes of the Greater Springfield area"
  "Community catchment description"
  "2017-2026"
  "https://www.springfieldlakesnaturecare.org.au/?page_id=9"
  Attribution.communitySource
  "Description of Mountain joining Opossum before Woogaroo; triangulate with mapped waterway assets."
  Attribution.publicAttribution

earthEmbeddingSourceAtlas : Attribution.AttributedSourceAtlas
earthEmbeddingSourceAtlas = Attribution.mkSourceAtlas
  "AlphaEarth-TESSERA physical geometry and Woogaroo source atlas"
  "DASHI.Geo.EarthEmbeddingAttributedSourcesExact"
  (alphaEarthPaper ∷ alphaEarthDocumentation ∷ tesseraOriginal ∷ tesseraV2 ∷
   rahmanPhysical ∷ rahmanGeometry ∷ ouZheng ∷ geoTesseraSoftware ∷
   woogarooCouncil ∷ springfieldEmergencyPlan ∷ springfieldNatureCare ∷ [])
  "Sources retain original author claims; DASHI geometry and evidence contracts remain separately authored."
