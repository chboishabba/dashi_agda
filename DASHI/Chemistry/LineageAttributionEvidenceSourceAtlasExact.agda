module DASHI.Chemistry.LineageAttributionEvidenceSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.KitzerowBH4ReactionSourceAtlasExact as BH4
import DASHI.Biology.IonicMimicrySourceAtlasExact as Ionic

------------------------------------------------------------------------
-- CROSS-TRANCHE ATTRIBUTED SOURCE ATLAS
--
-- Canonical identity owner for sources newly needed by the lineage/calibration
-- tranche. Existing BH4 and ionic-mimicry source identities are reused from
-- their original canonical owners rather than duplicated here.
------------------------------------------------------------------------

chlorAlkaliEuroChlor2022 : Source.AttributedSource
chlorAlkaliEuroChlor2022 =
  Source.mkNoDOISource
    "Euro Chlor / Cefic"
    "An Eco-profile and Environmental Product Declaration of the European Chlor-Alkali Industry: Chlorine (The Chlor-Alkali Process)"
    "Euro Chlor final report - updated September 2022"
    "2022"
    "https://www.eurochlor.org/wp-content/uploads/2022/09/Eco_profile-study-update-September-2022.pdf"
    Source.institutionalSource
    "technical/process source for European chlor-alkali electrolysis and its chlorine, sodium-hydroxide and hydrogen product context; does not pay DASHI atom lineage, exact half-reaction provenance, microkinetics or interfacial electron density"
    Source.publicAttribution

dhprBRENDA2026 : Source.AttributedSource
dhprBRENDA2026 =
  Source.mkNoDOISource
    "BRENDA Enzyme Database / IUBMB enzyme nomenclature"
    "EC 1.5.1.34 6,7-dihydropteridine reductase"
    "BRENDA enzyme entry EC 1.5.1.34"
    "2026"
    "https://www.brenda-enzymes.org/enzyme.php?ecno=1.5.1.34"
    Source.institutionalSource
    "curated DHPR reaction identity and NAD(P)H-linked tetrahydropteridine/dihydropteridine redox relation; does not pay organism-specific kinetics, in-vivo BH4 flux or exact electron-density trajectories"
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
    "broad review/primer source for carbon-rich terrestrial biochemistry and staged origin-of-life context; does not prove carbon uniqueness, abiogenesis, life inevitability or DASHI's matched carbon-vs-silicon benchmark"
    Source.publicAttribution

canonicalLineageCalibrationSources : List Source.AttributedSource
canonicalLineageCalibrationSources =
  chlorAlkaliEuroChlor2022
  ∷ BH4.aromaticHydroxylaseReview
  ∷ BH4.bRENDAspr
  ∷ dhprBRENDA2026
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
    "External sources pay only declared experimental, reaction-identity, structural, technical or review coordinates. Imported BH4/Pb-Ca identities retain their original owners. DASHI owns cross-source composition, lineage adapters, discriminator synthesis and formal non-promotion theorems."

atlasCreatesAuthority : Source.AttributedSourceAtlas → Bool
atlasCreatesAuthority = Source.atlasCreatesAuthority

canonicalAtlasNonPromoting :
  atlasCreatesAuthority canonicalLineageCalibrationSourceAtlas ≡ false
canonicalAtlasNonPromoting =
  Source.atlasCreatesAuthorityIsFalse canonicalLineageCalibrationSourceAtlas
