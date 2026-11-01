module DASHI.Reasoning.PathologicSourceAtlas where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Pathologic, theatricality, scarcity, perspective and typed-hyperfabric
-- source atlas.  Attribution records provenance only and imports no argument,
-- empirical result, artistic judgment or clinical authority as proof.
------------------------------------------------------------------------

pathologicGameSource : Source.AttributedSource
pathologicGameSource =
  Source.mkNoDOISource
    "Ice-Pick Lodge"
    "Pathologic (Мор. Утопия)"
    "Video game"
    "2005"
    "https://ice-pick.com/about-us/"
    (Source.namedSourceKind "video game")
    "primary work source for the twelve-day, three-healer, plague-town and route-indexed mechanics"
    Source.publicAttribution

pathologicClassicHDSource : Source.AttributedSource
pathologicClassicHDSource =
  Source.mkNoDOISource
    "Ice-Pick Lodge"
    "Pathologic Classic HD"
    "Video game"
    "2015"
    "https://store.steampowered.com/app/384110/Pathologic_Classic_HD/"
    (Source.namedSourceKind "video game")
    "primary work source for the revised English translation discussed in the attached review transcript"
    Source.publicAttribution

pathologic2Source : Source.AttributedSource
pathologic2Source =
  Source.mkNoDOISource
    "Ice-Pick Lodge"
    "Pathologic 2"
    "Video game"
    "2019"
    "https://www.pathologic-game.com/press/"
    (Source.namedSourceKind "video game")
    "primary work source for explicit theatrical framing and the reimagined Haruspex route"
    Source.publicAttribution

hbomberguyPathologicSource : Source.AttributedSource
hbomberguyPathologicSource =
  Source.mkNoDOISource
    "Harris Brewis (hbomberguy)"
    "Pathologic is Genius, And Here's Why"
    "YouTube video essay"
    "2019"
    "https://www.youtube.com/watch?v=JsNm2YLrk30"
    (Source.namedSourceKind "video essay")
    "supplied transcript source for disempowerment, recontextualisation, route asymmetry, jank, endings and player-developer metatheatre"
    Source.publicAttribution

novitzScarcitySource : Source.AttributedSource
novitzScarcitySource =
  Source.mkDOISource
    "Julian Novitz"
    "Scarcity and Survival Horror: Trade as an Instrument of Terror in Pathologic"
    "Transactions of the Digital Games Research Association 3(1)"
    "2017"
    "10.26503/todigra.v3i1.64"
    "https://doi.org/10.26503/todigra.v3i1.64"
    Source.academicArticleSource
    "scholarly calibration for scarcity, price movement, trade and anti-reward economy"
    Source.publicAttribution

kendallPathologicSource : Source.AttributedSource
kendallPathologicSource =
  Source.mkDOISource
    "Matthew Kendall"
    "Reading Pathologic 2: Russian Literature as a Trans-Medial Idea"
    "Russian Literature 138-139, 193-215"
    "2023"
    "10.1016/j.ruslit.2022.11.004"
    "https://doi.org/10.1016/j.ruslit.2022.11.004"
    Source.academicArticleSource
    "scholarly calibration for trans-medial literariness, narration and mediated interpretation"
    Source.publicAttribution

sheafHypergraphSource : Source.AttributedSource
sheafHypergraphSource =
  Source.mkDOISource
    "Iulia Duta, Giulia Cassarà, Fabrizio Silvestri and Pietro Liò"
    "Sheaf Hypergraph Networks"
    "arXiv:2309.17116"
    "2023"
    "10.48550/arXiv.2309.17116"
    "https://doi.org/10.48550/arXiv.2309.17116"
    Source.academicArticleSource
    "mathematical calibration for node and hyperedge stalks, incidence restriction maps and higher-order relations"
    Source.publicAttribution

beckmannPathologicSource : Source.AttributedSource
beckmannPathologicSource =
  Source.mkDOISource
    "Marie Beckmann"
    "Posthuman tragedy on the virtual stage in Pathologic 2"
    "International Journal of Performance Arts and Digital Media 21(3), 579-594"
    "2025"
    "10.1080/14794713.2025.2555035"
    "https://doi.org/10.1080/14794713.2025.2555035"
    Source.academicArticleSource
    "scholarly calibration for tragedy, posthumanism and narrative-dramatic agency"
    Source.publicAttribution

arevaloPortaPathologicSource : Source.AttributedSource
arevaloPortaPathologicSource =
  Source.mkDOISource
    "Alejandro Arévalo Arenas and Alberto Porta Pérez"
    "Performance in Multiple Realities: Theatrical Resource Inheritance in Pathologic 2"
    "Tecnología y Creatividad Aplicada 1(1)"
    "2025"
    "10.5281/zenodo.17483228"
    "https://doi.org/10.5281/zenodo.17483228"
    Source.academicArticleSource
    "scholarly calibration for theatricality, agency, performance layers and ludonarrative staging"
    Source.publicAttribution

lacanSinthomeSource : Source.AttributedSource
lacanSinthomeSource =
  Source.mkNoDOISource
    "Jacques Lacan"
    "The Seminar of Jacques Lacan, Book XXIII: The Sinthome"
    "Seminar delivered 1975-1976; translated editions vary"
    "1975-1976"
    "https://www.lacanonline.com/wp-content/uploads/2014/11/Seminar-XXIII-The-Sinthome-Jacques-Lacan-Thurston-translation.pdf"
    Source.academicBookSource
    "primary calibration for the sinthome as an additional stabilising knotting relation; no clinical application is imported"
    Source.publicAttribution

pathologicTypedDependencySources : List Source.AttributedSource
pathologicTypedDependencySources =
  pathologicGameSource
  ∷ pathologicClassicHDSource
  ∷ pathologic2Source
  ∷ hbomberguyPathologicSource
  ∷ novitzScarcitySource
  ∷ kendallPathologicSource
  ∷ sheafHypergraphSource
  ∷ beckmannPathologicSource
  ∷ arevaloPortaPathologicSource
  ∷ lacanSinthomeSource
  ∷ []

pathologicTypedDependencySourceAtlas : Source.AttributedSourceAtlas
pathologicTypedDependencySourceAtlas =
  Source.mkSourceAtlas
    "Pathologic, typed dependency, RSI and hyperfabric source atlas"
    "DASHI.Reasoning.PathologicSourceAtlas"
    pathologicTypedDependencySources
    "bounded attribution for game mechanics, review interpretation, scarcity, theatricality, perspective, hypergraphs and sinthomatic stabilisation"

pathologicTypedDependencySourceAtlasReceipt : GenericReceipt.GenericReceipt
pathologicTypedDependencySourceAtlasReceipt =
  Source.attributedSourceAtlasReceipt
    pathologicTypedDependencySourceAtlas
    "agda -i . DASHI/Reasoning/PathologicSourceAtlas.agda"

pathologicTypedDependencySourceAtlasReceiptNonPromoting :
  GenericReceipt.promotesClaim pathologicTypedDependencySourceAtlasReceipt ≡ false
pathologicTypedDependencySourceAtlasReceiptNonPromoting = refl
