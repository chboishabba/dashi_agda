module DASHI.Reasoning.KantLacanSourceAtlas where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Primary and scholarly calibration sources.
-- Bibliographic metadata and DOI records do not import arguments as proofs.
------------------------------------------------------------------------

kantPureReasonSource : Source.AttributedSource
kantPureReasonSource =
  Source.mkDOISource
    "Immanuel Kant; edited and translated by Paul Guyer and Allen W. Wood"
    "Critique of Pure Reason"
    "Cambridge Edition of the Works of Immanuel Kant"
    "1998"
    "10.1017/CBO9780511804649"
    "https://doi.org/10.1017/CBO9780511804649"
    Source.academicBookSource
    "primary calibration for categories, schemata, apperception, paralogism, antinomy, regulative ideas and transcendental illusion"
    Source.publicAttribution

kantJudgmentSource : Source.AttributedSource
kantJudgmentSource =
  Source.mkDOISource
    "Immanuel Kant; edited and translated by Paul Guyer; translated by Eric Matthews"
    "Critique of the Power of Judgment"
    "Cambridge Edition of the Works of Immanuel Kant"
    "2000"
    "10.1017/CBO9780511804656"
    "https://doi.org/10.1017/CBO9780511804656"
    Source.academicBookSource
    "primary calibration for reflective judgment and candidate universal search"
    Source.publicAttribution

lacanEcritsSource : Source.AttributedSource
lacanEcritsSource =
  Source.mkNoDOISource
    "Jacques Lacan; translated by Bruce Fink"
    "Écrits: The First Complete Edition in English"
    "W. W. Norton"
    "2006"
    "https://wwnorton.com/books/9780393329254"
    Source.academicBookSource
    "primary calibration for signifier, subject, Other and structural psychoanalytic vocabulary; no clinical diagnosis is imported"
    Source.publicAttribution

lacanSeminar17Source : Source.AttributedSource
lacanSeminar17Source =
  Source.mkNoDOISource
    "Jacques Lacan; translated by Russell Grigg"
    "The Seminar of Jacques Lacan, Book XVII: The Other Side of Psychoanalysis"
    "W. W. Norton"
    "2007"
    "https://wwnorton.com/books/9780393325368"
    Source.academicBookSource
    "primary calibration for the four discourse mathemes and their structural positions"
    Source.publicAttribution

lacanSeminar20Source : Source.AttributedSource
lacanSeminar20Source =
  Source.mkNoDOISource
    "Jacques Lacan; translated by Bruce Fink"
    "The Seminar of Jacques Lacan, Book XX: Encore—On Feminine Sexuality, the Limits of Love and Knowledge"
    "W. W. Norton"
    "1998"
    "https://wwnorton.com/books/9780393319163"
    Source.academicBookSource
    "primary calibration for non-all, sexual non-rapport and limits of signifying totalisation"
    Source.publicAttribution

vanheuleCapitalistDiscourseSource : Source.AttributedSource
vanheuleCapitalistDiscourseSource =
  Source.mkDOISource
    "Stijn Vanheule"
    "Capitalist Discourse, Subjectivity and Lacanian Psychoanalysis"
    "Frontiers in Psychology 7:1948"
    "2016"
    "10.3389/fpsyg.2016.01948"
    "https://doi.org/10.3389/fpsyg.2016.01948"
    Source.academicArticleSource
    "scholarly calibration for the standard discourse rotation and the separately governed capitalist-discourse mutation"
    Source.publicAttribution

conwayNortonMoonshineSource : Source.AttributedSource
conwayNortonMoonshineSource =
  Source.mkDOISource
    "John H. Conway and Simon P. Norton"
    "Monstrous Moonshine"
    "Bulletin of the London Mathematical Society 11(3), 308–339"
    "1979"
    "10.1112/blms/11.3.308"
    "https://doi.org/10.1112/blms/11.3.308"
    Source.academicArticleSource
    "source calibration for the moonshine coefficient setting; stage place-value semantics are not imported"
    Source.publicAttribution

borcherdsMoonshineSource : Source.AttributedSource
borcherdsMoonshineSource =
  Source.mkDOISource
    "Richard E. Borcherds"
    "Monstrous Moonshine and Monstrous Lie Superalgebras"
    "Inventiones Mathematicae 109, 405–444"
    "1992"
    "10.1007/BF01232032"
    "https://doi.org/10.1007/BF01232032"
    Source.academicArticleSource
    "proof source for monstrous moonshine; the local J-plus-one stage bridge imports only exact finite arithmetic"
    Source.publicAttribution

greenshieldsTopologySource : Source.AttributedSource
greenshieldsTopologySource =
  Source.mkDOISource
    "Will Greenshields"
    "Writing the Structures of the Subject: Lacan and Topology"
    "Palgrave Macmillan"
    "2017"
    "10.1007/978-3-319-47533-2"
    "https://doi.org/10.1007/978-3-319-47533-2"
    Source.academicBookSource
    "calibrates Lacan's topological programme; this tranche exposes an RSI dependency hyperlink but not a Borromean link proof"
    Source.publicAttribution

kantLacanSources : List Source.AttributedSource
kantLacanSources =
  kantPureReasonSource
  ∷ kantJudgmentSource
  ∷ lacanEcritsSource
  ∷ lacanSeminar17Source
  ∷ lacanSeminar20Source
  ∷ vanheuleCapitalistDiscourseSource
  ∷ conwayNortonMoonshineSource
  ∷ borcherdsMoonshineSource
  ∷ greenshieldsTopologySource
  ∷ []

kantLacanSourceAtlas : Source.AttributedSourceAtlas
kantLacanSourceAtlas =
  Source.mkSourceAtlas
    "Kant, Lacan, discourse, stage-012 and j-plus-one source atlas"
    "DASHI.Reasoning.KantLacanSourceAtlas"
    kantLacanSources
    "bounded attribution for critical synthesis, discourse algebra, RSI topology and moonshine arithmetic"

kantLacanSourceAtlasReceipt : GenericReceipt.GenericReceipt
kantLacanSourceAtlasReceipt =
  Source.attributedSourceAtlasReceipt
    kantLacanSourceAtlas
    "agda -i . DASHI/Reasoning/KantLacanSourceAtlas.agda"

kantLacanSourceAtlasReceiptNonPromoting :
  GenericReceipt.promotesClaim kantLacanSourceAtlasReceipt ≡ false
kantLacanSourceAtlasReceiptNonPromoting = refl
