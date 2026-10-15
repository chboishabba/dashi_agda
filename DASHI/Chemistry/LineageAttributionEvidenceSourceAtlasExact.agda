module DASHI.Chemistry.LineageAttributionEvidenceSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.KitzerowBH4ReactionSourceAtlasExact as BH4
import DASHI.Biology.IonicMimicrySourceAtlasExact as Ionic

------------------------------------------------------------------------
-- CROSS-TRANCHE ATTRIBUTED SOURCE ATLAS
--
-- Existing attributed sources are imported rather than copied/re-authored.
-- New rows are added only where this tranche needs an external source that did
-- not already have a canonical attributed owner.
------------------------------------------------------------------------

chlorAlkaliBREF2014 : Source.AttributedSource
chlorAlkaliBREF2014 =
  Source.mkDOISource
    "Thomas Brinkmann; Luis Delgado Sancho; Germán Giner Santonja; Serge Roudier; Frauke Schorcht"
    "Best Available Techniques (BAT) Reference Document for the Production of Chlor-alkali"
    "European Commission Joint Research Centre, EUR 26844 EN"
    "2014"
    "10.2791/13138"
    "https://publications.jrc.ec.europa.eu/repository/handle/JRC91156"
    Source.governmentSource
    "External technical authority that chlor-alkali production uses brine electrolysis and produces chlorine/hydrogen/caustic streams. DASHI owns the typed half-reaction composition and lineage adapters; this source does not pay cell-specific kinetics or interfacial electron-density trajectories."
    Source.publicAttribution

dhprBRENDA : Source.AttributedSource
dhprBRENDA =
  Source.mkNoDOISource
    "BRENDA Enzyme Database / IUBMB enzyme nomenclature"
    "EC 1.5.1.34 6,7-dihydropteridine reductase"
    "BRENDA enzyme entry; EC 1.5.1.34"
    "2026"
    "https://www.brenda-enzymes.org/enzyme.php?ecno=1.5.1.34"
    Source.institutionalSource
    "Curated DHPR reaction identity and NAD(P)H-linked tetrahydropteridine/dihydropteridine redox relation. This database row does not pay organism-specific kinetics, in-vivo BH4 flux, or exact electron-density trajectories."
    Source.publicAttribution

astrobiologyPrimer2016 : Source.AttributedSource
astrobiologyPrimer2016 =
  Source.mkDOISource
    "Shawn D. Domagal-Goldman; Katherine E. Wright; Katarzyna Adamala; et al."
    "The Astrobiology Primer v2.0"
    "Astrobiology 16(8):561-653"
    "2016"
    "10.1089/ast.2015.1460"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC5008114/"
    Source.academicArticleSource
    "Broad review/primer authority for carbon-rich terrestrial biochemistry and origin-of-life context. It does not prove carbon uniqueness, life inevitability, or DASHI's carbon-versus-silicon reachable-chemistry benchmark."
    Source.publicAttribution

canonicalLineageCalibrationSources : List Source.AttributedSource
canonicalLineageCalibrationSources =
  chlorAlkaliBREF2014
  ∷ BH4.aromaticHydroxylaseReview
  ∷ BH4.bRENDAspr
  ∷ dhprBRENDA
  ∷ BH4.nosReview
  ∷ BH4.agmoReview
  ∷ Ionic.habermannEtAl1983
  ∷ Ionic.kirbergerYang2008
  ∷ Ionic.moralesEtAl2011
  ∷ Ionic.kumarEtAl2012
  ∷ Ionic.dudevGrauffelLim2018
  ∷ astrobiologyPrimer2016
  ∷ []

canonicalLineageCalibrationSourceAtlas : Source.AttributedSourceAtlas
canonicalLineageCalibrationSourceAtlas =
  Source.mkSourceAtlas
    "atomic-molecular-reaction lineage calibration attributed source atlas"
    "DASHI.Chemistry.LineageAttributionEvidenceSourceAtlasExact"
    canonicalLineageCalibrationSources
    "External sources pay only their declared experimental, reaction-identity, structural, technical or review coordinates. Imported BH4/Pb-Ca source identities retain their original owners. DASHI owns cross-source composition, lineage hyperfabric adapters, discriminator synthesis and formal non-promotion theorems."

atlasCreatesAuthority : Source.AttributedSourceAtlas → Bool
atlasCreatesAuthority = Source.atlasCreatesAuthority

canonicalAtlasNonPromoting :
  atlasCreatesAuthority canonicalLineageCalibrationSourceAtlas ≡ false
canonicalAtlasNonPromoting =
  Source.atlasCreatesAuthorityIsFalse canonicalLineageCalibrationSourceAtlas
