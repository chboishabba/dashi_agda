module DASHI.Environment.BiocontrolExternalityExperimentSourceAtlasExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- ATTRIBUTION BOUNDARY
--
-- External sources below retain identity, source kind, relationship and
-- visibility through the repo-wide AttributedSource/Snowball machinery.
-- They supply empirical, historical, regulatory, operational, or literature
-- context only.
--
-- The finite non-factorability witnesses, consumer-indexed discriminator
-- selection, selective reopening, chemistry-indexing and costed experiment-
-- search constructions in this tranche are DASHI synthetic extensions.
------------------------------------------------------------------------

csiroHyacinthSource : Attribution.AttributedSource
csiroHyacinthSource = Attribution.mkNoDOISource
  "CSIRO"
  "Water hyacinth"
  "CSIRO biological control resource"
  "year not recorded on source surface"
  "https://ento.csiro.au/biocontrol/hyacinth.html"
  Attribution.institutionalSource
  "historical Australian water-hyacinth biological-control programme and agent context; not a source for DASHI non-factorability or experiment-search theorems"
  Attribution.publicAttribution

australianManagementGuideSource : Attribution.AttributedSource
australianManagementGuideSource = Attribution.mkNoDOISource
  "Andrew Petroeschevsky (compiler); Tobias Bickel, Darren Jennings, Stephen Johnson, Reece Luxton, Kay Bailey (listed information/guide revision contributors)"
  "Weed Management Guide - Water Hyacinth"
  "Commonwealth of Australia / Weed of National Significance management guide"
  "year not recorded in supplied guide"
  "user-supplied PDF: Weed Management Guide - Water Hyacinth"
  Attribution.governmentSource
  "Australian control methods; Neochetina damage/sinking mechanism; decomposition/dissolved-oxygen warning; seedbank persistence; nutrient context; integrated management and Sandringham Lagoon restoration case"
  Attribution.publicAttribution

daffBiocontrolAgentsSource : Attribution.AttributedSource
daffBiocontrolAgentsSource = Attribution.mkNoDOISource
  "Australian Government Department of Agriculture, Fisheries and Forestry"
  "Biological control agents"
  "Australian biosecurity risk-analysis guidance"
  "current institutional web resource; atlas does not infer publication year"
  "https://www.agriculture.gov.au/biosecurity/risk-analysis/biological-control-agents"
  Attribution.governmentSource
  "contemporary Australian host-specificity/off-target risk-analysis governance context; not retroactive proof of safety for historic releases"
  Attribution.publicAttribution

deLoach1976Source : Attribution.AttributedSource
deLoach1976Source = Attribution.mkDOISource
  "C. J. DeLoach"
  "Neochetina bruchi, a Biological Control Agent of Waterhyacinth: Host Specificity in Argentina"
  "Annals of the Entomological Society of America 69(4), 635-642"
  "1976"
  "10.1093/aesa/69.4.635"
  "https://doi.org/10.1093/aesa/69.4.635"
  Attribution.academicArticleSource
  "host-specificity evidence calibration for N. bruchi; does not pay general post-release safety or net ecosystem benefit"
  Attribution.publicAttribution

ogutuOhwayo2002Source : Attribution.AttributedSource
ogutuOhwayo2002Source = Attribution.mkNoDOISource
  "R. Ogutu-Ohwayo; J. S. Balirwa; T. Twongo; R. Mugidde; Odongkara (initial varies across indexed records)"
  "Impact of dead and sunken water hyacinth on biotic communities, the aquatic environment and socio-economic activities"
  "Fisheries Resources Research Institute, Jinja, Uganda / Lake Victoria Environmental Management Project"
  "2002"
  "http://hdl.handle.net/1834/33023"
  (Attribution.namedSourceKind "research institute report")
  "dead/sunken biomass, dissolved-oxygen, nutrient and aquatic-community impact context; indexed author-initial ambiguity is retained rather than silently reconciled"
  Attribution.publicAttribution

centerEtAl2005Source : Attribution.AttributedSource
centerEtAl2005Source = Attribution.mkDOISource
  "Ted D. Center; Thai K. Van; F. Allen Dray Jr.; Steven J. Franks; M. Teresa Rebelo; Paul D. Pratt; Min B. Rayamajhi"
  "Herbivory alters competitive interactions between two invasive aquatic plants"
  "Biological Control 33(2), 173-185"
  "2005"
  "10.1016/j.biocontrol.2005.02.005"
  "https://doi.org/10.1016/j.biocontrol.2005.02.005"
  Attribution.academicArticleSource
  "calibrates the community-reassembly axis by showing that herbivory can alter competition between aquatic invaders; not a theorem that a particular Australian site will follow that trajectory"
  Attribution.publicAttribution

chalaEtAl2026Source : Attribution.AttributedSource
chalaEtAl2026Source = Attribution.mkDOISource
  "Desalegn Chala; Diress Tsegaye; Habtamu Alem; et al."
  "Beyond Removal: Strategies for Sustainable Control of Water Hyacinth in Tropical Freshwater Ecosystems"
  "Environmental Management 76, article 187"
  "2026"
  "10.1007/s00267-026-02494-1"
  "https://doi.org/10.1007/s00267-026-02494-1"
  Attribution.academicArticleSource
  "sustainable-control synthesis and beyond-removal/nutrient-recycling context; motivates retaining system-level outcome coordinates without importing DASHI mathematics"
  Attribution.publicAttribution

marianiEtAl2026Source : Attribution.AttributedSource
marianiEtAl2026Source = Attribution.mkDOISource
  "F. Mariani; E. G. Steen; B. G. Rector; P. D. Pratt; R. Diaz"
  "Too hot, too tough, too crowded: Abiotic and biotic constraints on Niphograpta albiguttalis establishment on water hyacinth (Pontederia crassipes) in the southeastern United States"
  "Biological Control 216, 106023"
  "2026"
  "10.1016/j.biocontrol.2026.106023"
  "https://doi.org/10.1016/j.biocontrol.2026.106023"
  Attribution.academicArticleSource
  "agent-interaction and abiotic-context calibration from a southeastern-US field setting; no geographic transfer to Australia is asserted by the atlas"
  Attribution.publicAttribution

ipswichSpringfield2025Source : Attribution.AttributedSource
ipswichSpringfield2025Source = Attribution.mkNoDOISource
  "Ipswich City Council"
  "Strides made in salvinia weed management across Springfield Lakes waterways"
  "Ipswich City Council news release"
  "2025"
  "https://www.ipswich.qld.gov.au/News-Articles-Folder/2025/Strides-made-in-salvinia-weed-management-across-Springfield-Lakes-waterways"
  Attribution.governmentSource
  "local Springfield Lakes operational record for SALVINIA mechanical removal using a spider excavator and aquatic weed harvester; supports access/equipment/biomass-export context only and is not water-hyacinth efficacy evidence"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- One canonical atlas: absence of DOI is atlas-local, and none of the rows
-- creates proof, exhaustive coverage, endorsement, or deployment authority.
------------------------------------------------------------------------

canonicalBiocontrolSourceAtlas : Attribution.AttributedSourceAtlas
canonicalBiocontrolSourceAtlas = Attribution.mkSourceAtlas
  "water-hyacinth biocontrol externality source atlas"
  "DASHI.Environment.BiocontrolExternalityExperimentSourceAtlasExact"
  (csiroHyacinthSource
    ∷ australianManagementGuideSource
    ∷ daffBiocontrolAgentsSource
    ∷ deLoach1976Source
    ∷ ogutuOhwayo2002Source
    ∷ centerEtAl2005Source
    ∷ chalaEtAl2026Source
    ∷ marianiEtAl2026Source
    ∷ ipswichSpringfield2025Source
    ∷ [])
  "source-bound context for programme history, Australian management mechanisms/governance, host specificity, biomass fate, community competition, nutrient recycling, agent interaction and local mechanical-removal operations; DASHI finite witnesses and experiment-search results remain repository-native extensions"

------------------------------------------------------------------------
-- Snowball receipts preserve source role through downstream projection.
------------------------------------------------------------------------

csiroHyacinthSnowballReceipt : Snowball.SourceRoleSnowballReceipt csiroHyacinthSource
csiroHyacinthSnowballReceipt = Snowball.canonicalSourceRoleSnowballReceipt csiroHyacinthSource

australianManagementGuideSnowballReceipt :
  Snowball.SourceRoleSnowballReceipt australianManagementGuideSource
australianManagementGuideSnowballReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt australianManagementGuideSource

daffBiocontrolAgentsSnowballReceipt : Snowball.SourceRoleSnowballReceipt daffBiocontrolAgentsSource
daffBiocontrolAgentsSnowballReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt daffBiocontrolAgentsSource

deLoach1976SnowballReceipt : Snowball.SourceRoleSnowballReceipt deLoach1976Source
deLoach1976SnowballReceipt = Snowball.canonicalSourceRoleSnowballReceipt deLoach1976Source

ogutuOhwayo2002SnowballReceipt : Snowball.SourceRoleSnowballReceipt ogutuOhwayo2002Source
ogutuOhwayo2002SnowballReceipt = Snowball.canonicalSourceRoleSnowballReceipt ogutuOhwayo2002Source

centerEtAl2005SnowballReceipt : Snowball.SourceRoleSnowballReceipt centerEtAl2005Source
centerEtAl2005SnowballReceipt = Snowball.canonicalSourceRoleSnowballReceipt centerEtAl2005Source

chalaEtAl2026SnowballReceipt : Snowball.SourceRoleSnowballReceipt chalaEtAl2026Source
chalaEtAl2026SnowballReceipt = Snowball.canonicalSourceRoleSnowballReceipt chalaEtAl2026Source

marianiEtAl2026SnowballReceipt : Snowball.SourceRoleSnowballReceipt marianiEtAl2026Source
marianiEtAl2026SnowballReceipt = Snowball.canonicalSourceRoleSnowballReceipt marianiEtAl2026Source

ipswichSpringfield2025SnowballReceipt :
  Snowball.SourceRoleSnowballReceipt ipswichSpringfield2025Source
ipswichSpringfield2025SnowballReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt ipswichSpringfield2025Source

record SourceAtlasBoundary : Set where
  constructor sourceAtlasBoundary
  field
    sourceRolesSnowball : Bool
    sourceRolesSnowballIsTrue : sourceRolesSnowball ≡ true
    externalSourcesOwnDashIExtensionTheorems : Bool
    externalSourcesOwnDashIExtensionTheoremsIsFalse : externalSourcesOwnDashIExtensionTheorems ≡ false
    citationImportsEmpiricalUniversality : Bool
    citationImportsEmpiricalUniversalityIsFalse : citationImportsEmpiricalUniversality ≡ false
    citationCreatesDeploymentAuthority : Bool
    citationCreatesDeploymentAuthorityIsFalse : citationCreatesDeploymentAuthority ≡ false

canonicalSourceAtlasBoundary : SourceAtlasBoundary
canonicalSourceAtlasBoundary = sourceAtlasBoundary true refl false refl false refl false refl
