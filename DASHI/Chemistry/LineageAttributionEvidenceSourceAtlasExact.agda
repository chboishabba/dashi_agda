module DASHI.Chemistry.LineageAttributionEvidenceSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Chemistry.LineageCalibrationAttributionEnvelopeExact as Existing
import DASHI.Biology.KitzerowBH4ReactionSourceAtlasExact as BH4
import DASHI.Biology.IonicMimicrySourceAtlasExact as Ionic

------------------------------------------------------------------------
-- CROSS-TRANCHE ATTRIBUTED SOURCE ATLAS
--
-- This is an aggregation layer, not a second identity registry. Sources that
-- already have canonical attributed owners are reused definitionally.
------------------------------------------------------------------------

chlorAlkaliBREF2014 : Source.AttributedSource
chlorAlkaliBREF2014 = Existing.chlorAlkaliEuroChlor2022

dhprBRENDA : Source.AttributedSource
dhprBRENDA = Existing.dhprBrenda2026

astrobiologyPrimer2016 : Source.AttributedSource
astrobiologyPrimer2016 = Existing.astrobiologyPrimer2016

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
    "Aggregation only: external sources pay declared experimental, reaction-identity, structural, technical or review coordinates. Existing source identities retain their canonical owners. DASHI owns cross-source composition, lineage hyperfabric adapters, discriminator synthesis and formal non-promotion theorems."

atlasCreatesAuthority : Source.AttributedSourceAtlas → Bool
atlasCreatesAuthority = Source.atlasCreatesAuthority

canonicalAtlasNonPromoting :
  atlasCreatesAuthority canonicalLineageCalibrationSourceAtlas ≡ false
canonicalAtlasNonPromoting =
  Source.atlasCreatesAuthorityIsFalse canonicalLineageCalibrationSourceAtlas
