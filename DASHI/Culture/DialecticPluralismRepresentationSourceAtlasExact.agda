module DASHI.Culture.DialecticPluralismRepresentationSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- DIALECTIC / PLURALISM / REPRESENTATION SOURCE ATLAS
--
-- Attribution discipline:
--   historical author / artist / presenter
--   != later interpreter
--   != museum/publisher/access carrier
--   != DASHI formal construction
--   != universal doctrine or empirical law.
--
-- Where exact primary-text passage recovery is incomplete, the atlas says so
-- instead of silently promoting secondary scholarship into primary authorship.
------------------------------------------------------------------------

hegelDialecticsSecondarySource : Source.AttributedSource
hegelDialecticsSecondarySource =
  Source.mkNoDOISource
    "Julie E. Maybee"
    "Hegel's Dialectics"
    "Stanford Encyclopedia of Philosophy"
    "2016; substantive revision 2020"
    "https://plato.stanford.edu/entries/hegel-dialectics/"
    Source.academicArticleSource
    "secondary source for Hegelian dialectic as a contradictory/oppositional process; DASHI does not attribute the textbook thesis-antithesis-synthesis formula to Hegel on this basis"
    Source.publicAttribution

hegelPrimaryWorkCarrier : Source.AttributedSource
hegelPrimaryWorkCarrier =
  Source.mkNoDOISource
    "G. W. F. Hegel"
    "Science of Logic"
    "primary philosophical work; original German publication 1812-1816"
    "1812-1816"
    "https://www.marxists.org/reference/archive/hegel/works/hl/hlconten.htm"
    Source.academicBookSource
    "primary-work carrier for dialectic/negation/contradiction investigation; exact passage-level promotion remains a separate source-recovery obligation"
    Source.publicAttribution

zizekDialecticalMaterialismSource : Source.AttributedSource
zizekDialecticalMaterialismSource =
  Source.mkNoDOISource
    "Slavoj Žižek"
    "Less Than Nothing: Hegel and the Shadow of Dialectical Materialism"
    "Verso"
    "2012 / paperback 2013"
    "https://www.versobooks.com/en-gb/products/2241-less-than-nothing"
    Source.academicBookSource
    "primary author/publisher carrier showing Žižek explicitly frames the project through Hegel and dialectical materialism; exact substantive theses require passage-level receipts"
    Source.publicAttribution

hoeMathLevelsSource : Source.AttributedSource
hoeMathLevelsSource =
  Source.mkNoDOISource
    "hoe_math"
    "LEVELS [1: INTRODUCTION]"
    "itishoemath.com"
    "2025-2026 web publication; model circulated earlier in video/chart form"
    "https://itishoemath.com/levels-1-introduction/"
    Source.practitionerSource
    "presenter-owned explanation and simplification of staged psychological-development material; the presenter explicitly describes the model as theoretical and based on multiple researchers"
    Source.publicAttribution

hoeMathLevelsChartSource : Source.AttributedSource
hoeMathLevelsChartSource =
  Source.mkNoDOISource
    "hoe_math"
    "FREE Levels Chart"
    "itishoemath.com"
    "2025-2026"
    "https://itishoemath.com/free-levels-chart/"
    Source.practitionerSource
    "assembled pedagogical chart with separately labelled Spiral Dynamics, developmental-level and AQAL components; underlying named traditions retain their own source authorship"
    Source.publicAttribution

magrittePipeSource : Source.AttributedSource
magrittePipeSource =
  Source.mkNoDOISource
    "René Magritte"
    "The Treachery of Images (This is Not a Pipe)"
    "Los Angeles County Museum of Art collection record"
    "1929"
    "https://collections.lacma.org/object/31931"
    Source.institutionalSource
    "museum carrier for Magritte's work; bounded relevance is separation of represented object, image and linguistic inscription; museum interpretation is not silently promoted to artist-authored prose"
    Source.publicAttribution

duchampFountainSource : Source.AttributedSource
duchampFountainSource =
  Source.mkNoDOISource
    "Marcel Duchamp"
    "Fountain"
    "1917 readymade; museum documentation via SFMOMA/MoMA"
    "1917"
    "https://www.sfmoma.org/artwork/98.291"
    Source.institutionalSource
    "museum carrier for Duchamp's readymade challenge to object/art-status and artist-selection relations; later replicas/reconstructions retain their own object dates without replacing the 1917 work's historical attribution"
    Source.publicAttribution

kosuthChairSource : Source.AttributedSource
kosuthChairSource =
  Source.mkNoDOISource
    "Joseph Kosuth"
    "One and Three Chairs"
    "The Museum of Modern Art collection record"
    "1965"
    "https://www.moma.org/collection/works/81435"
    Source.institutionalSource
    "museum carrier for one chair presented across object, photograph and dictionary-definition registers; DASHI uses this only as representation-layer calibration"
    Source.publicAttribution

rauschenbergErasureSource : Source.AttributedSource
rauschenbergErasureSource =
  Source.mkNoDOISource
    "Robert Rauschenberg; source drawing by Willem de Kooning; label devised with Jasper Johns"
    "Erased de Kooning Drawing"
    "San Francisco Museum of Modern Art collection record"
    "1953"
    "https://www.sfmoma.org/artwork/98.298/"
    Source.institutionalSource
    "museum carrier for an artwork whose meaning depends on provenance, erasure event and label/history; authorship of component acts remains distributed rather than collapsed into one name"
    Source.publicAttribution

foucaultPipeSource : Source.AttributedSource
foucaultPipeSource =
  Source.mkNoDOISource
    "Michel Foucault; illustrations and letters by René Magritte; trans./ed. James Harkness"
    "This Is Not a Pipe"
    "University of California Press; French original Ceci n'est pas une pipe, Fata Morgana 1973"
    "1973; English edition 1983; later UC Press editions"
    "https://www.ucpress.edu/books/this-is-not-a-pipe/paper"
    Source.academicBookSource
    "primary Foucault interpretive engagement with Magritte on pictorial reference/language; Foucault's interpretation does not become Magritte's own proposition"
    Source.publicAttribution

allSources : List Source.AttributedSource
allSources =
  hegelDialecticsSecondarySource
  ∷ hegelPrimaryWorkCarrier
  ∷ zizekDialecticalMaterialismSource
  ∷ hoeMathLevelsSource
  ∷ hoeMathLevelsChartSource
  ∷ magrittePipeSource
  ∷ duchampFountainSource
  ∷ kosuthChairSource
  ∷ rauschenbergErasureSource
  ∷ foucaultPipeSource
  ∷ []

sourceAtlas : Source.AttributedSourceAtlas
sourceAtlas =
  Source.mkSourceAtlas
    "dialectic / pluralism / representation source atlas"
    "DASHI.Culture.DialecticPluralismRepresentationSourceAtlasExact"
    allSources
    "bounded attribution for Hegel/dialectic, Žižek/dialectical materialism, hoe_math Levels, Magritte/Duchamp/Kosuth/Rauschenberg representation and Foucault's Magritte interpretation"

sourceAtlasReceipt : GenericReceipt.GenericReceipt
sourceAtlasReceipt =
  Source.attributedSourceAtlasReceipt
    sourceAtlas
    "agda -i . -l standard-library DASHI/Culture/DialecticPluralismRepresentationSourceAtlasExact.agda"

sourceAtlasReceiptNonPromoting :
  GenericReceipt.promotesClaim sourceAtlasReceipt ≡ false
sourceAtlasReceiptNonPromoting = refl

------------------------------------------------------------------------
-- Explicit attribution firewalls.
------------------------------------------------------------------------

data SecondaryHegelSummaryIsPrimaryHegelSentence : Set where
data ThesisAntithesisSynthesisIsAutomaticallyHegel : Set where
data ZizekBookTitleProvesAllDialecticalMaterialismClaims : Set where
data HoeMathChartIsOriginalResearchForEveryLevel : Set where
data SpiralDynamicsAQALAuthorsOwnHoeMathAssembly : Set where
data MuseumDescriptionCreatesArtistIntention : Set where
data FoucaultInterpretationBecomesMagritteIntention : Set where
data ReplicaDateReplacesDuchamp1917OriginalDate : Set where

secondaryHegelDoesNotBecomePrimarySentence :
  SecondaryHegelSummaryIsPrimaryHegelSentence → ⊥
secondaryHegelDoesNotBecomePrimarySentence ()

thesisAntithesisSynthesisNotAutoAttributedToHegel :
  ThesisAntithesisSynthesisIsAutomaticallyHegel → ⊥
thesisAntithesisSynthesisNotAutoAttributedToHegel ()

zizekTitleDoesNotProveAllMaterialistClaims :
  ZizekBookTitleProvesAllDialecticalMaterialismClaims → ⊥
zizekTitleDoesNotProveAllMaterialistClaims ()

hoeMathChartDoesNotOwnAllUnderlyingResearch :
  HoeMathChartIsOriginalResearchForEveryLevel → ⊥
hoeMathChartDoesNotOwnAllUnderlyingResearch ()

underlyingTraditionsDoNotOwnHoeMathAssembly :
  SpiralDynamicsAQALAuthorsOwnHoeMathAssembly → ⊥
underlyingTraditionsDoNotOwnHoeMathAssembly ()

museumDescriptionDoesNotCreateArtistIntention :
  MuseumDescriptionCreatesArtistIntention → ⊥
museumDescriptionDoesNotCreateArtistIntention ()

foucaultDoesNotBecomeMagritte :
  FoucaultInterpretationBecomesMagritteIntention → ⊥
foucaultDoesNotBecomeMagritte ()

replicaDateDoesNotReplaceOriginalFountainDate :
  ReplicaDateReplacesDuchamp1917OriginalDate → ⊥
replicaDateDoesNotReplaceOriginalFountainDate ()
