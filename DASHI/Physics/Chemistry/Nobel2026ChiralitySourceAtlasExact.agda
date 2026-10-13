module DASHI.Physics.Chemistry.Nobel2026ChiralitySourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- ATTRIBUTED SOURCE ATLAS
-- Source identity and source-role attribution are kept on the repository-wide
-- AttributedSource surface.  Citations do not import proof authority.
------------------------------------------------------------------------

nobel2026Announcement : Source.AttributedSource
nobel2026Announcement =
  Source.mkNoDOISource
    "Royal Swedish Academy of Sciences"
    "The Nobel Prize in Chemistry 2026"
    "Kungl. Vetenskapsakademien"
    "2026"
    "https://www.kva.se/en/news/the-nobel-prize-in-chemistry-2026/"
    Source.institutionalSource
    "award identity and official motivation: Kagan and Soai; nonlinear effects and autocatalysis in asymmetric organic synthesis"
    Source.publicAttribution

kagan1986 : Source.AttributedSource
kagan1986 =
  Source.mkDOISource
    "C. Puchot; O. Samuel; E. Dunach; S. Zhao; C. Agami; H. B. Kagan"
    "Nonlinear effects in asymmetric synthesis. Examples in asymmetric oxidations and aldolization reactions"
    "Journal of the American Chemical Society 108(9), 2353-2357"
    "1986"
    "10.1021/ja00269a036"
    "https://doi.org/10.1021/ja00269a036"
    Source.academicArticleSource
    "primary nonlinear-effect source; pays source identity of asymmetric-catalysis NLE observations, not a universal response law"
    Source.publicAttribution

soai1995 : Source.AttributedSource
soai1995 =
  Source.mkDOISource
    "Kenso Soai; Takanori Shibata; Hiroshi Morioka; Kaori Choji"
    "Asymmetric autocatalysis and amplification of enantiomeric excess of a chiral molecule"
    "Nature 378, 767-768"
    "1995"
    "10.1038/378767a0"
    "https://doi.org/10.1038/378767a0"
    Source.academicArticleSource
    "primary asymmetric-autocatalysis source; product alcohol participates in its own asymmetric formation and amplifies ee"
    Source.publicAttribution

sato2003 : Source.AttributedSource
sato2003 =
  Source.mkDOISource
    "I. Sato; H. Urabe; S. Ishiguro; T. Shibata; K. Soai"
    "Amplification of Chirality from Extremely Low to Greater than 99.5% ee by Asymmetric Autocatalysis"
    "Angewandte Chemie International Edition 42, 315-317"
    "2003"
    "10.1002/anie.200390105"
    "https://doi.org/10.1002/anie.200390105"
    Source.academicArticleSource
    "primary quantitative amplification source: about 0.00005% ee to greater than 99.5% ee after three cycles"
    Source.publicAttribution

buonoBlackmond2003 : Source.AttributedSource
buonoBlackmond2003 =
  Source.mkDOISource
    "F. G. Buono; D. G. Blackmond"
    "Kinetic Evidence for a Tetrameric Transition State in the Asymmetric Autocatalytic Alkylation of Pyrimidyl Aldehydes"
    "Journal of the American Chemical Society"
    "2003"
    "10.1021/ja034705n"
    "https://doi.org/10.1021/ja034705n"
    Source.academicArticleSource
    "kinetic/modeling evidence relevant to aggregation and nonlinear amplification; does not settle all later mechanistic alternatives"
    Source.publicAttribution

mohler2025 : Source.AttributedSource
mohler2025 =
  Source.mkDOISource
    "Patrick Mohler; Gloria Betzenbichler; Laura Huber; Alexander F. Siegle; Oliver Trapp"
    "Mechanistic analysis and kinetic profiling of Soai's asymmetric autocatalysis for pyridyl and pyrimidyl substrates"
    "Nature Communications 16, 7303"
    "2025"
    "10.1038/s41467-025-62591-3"
    "https://doi.org/10.1038/s41467-025-62591-3"
    Source.academicArticleSource
    "same-reaction mechanistic/kinetic source: in-situ HRMS, multiplexing HPLC, reaction-network simulation, transient zinc hemiacetalate intermediates, source-exposed ODE and rate-role facts"
    Source.publicAttribution

nobel2026ChiralityAtlas : Source.AttributedSourceAtlas
nobel2026ChiralityAtlas =
  Source.mkSourceAtlas
    "2026 Nobel asymmetric synthesis / autocatalysis source atlas"
    "DASHI.Physics.Chemistry.Nobel2026ChiralitySourceAtlasExact"
    (nobel2026Announcement ∷
     kagan1986 ∷
     soai1995 ∷
     sato2003 ∷
     buonoBlackmond2003 ∷
     mohler2025 ∷ [])
    "award attribution, primary nonlinear-effect/autocatalysis experiments, high-amplification experiment, aggregation kinetics, and modern same-reaction mechanistic profiling"

sourceCountIsSix : Source.sourceCount (Source.sources nobel2026ChiralityAtlas) ≡ 6
sourceCountIsSix = refl

atlasDoesNotImportProof :
  Receipt.promotesClaim
    (Source.attributedSourceAtlasReceipt
      nobel2026ChiralityAtlas
      "source atlas static receipt")
  ≡ false
atlasDoesNotImportProof =
  Source.attributedSourceAtlasReceiptNonPromoting
    nobel2026ChiralityAtlas
    "source atlas static receipt"
