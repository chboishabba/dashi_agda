module DASHI.Reasoning.ZizekPNFSourceAtlas where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Attribution and calibration sources.
--
-- The first two entries record the user-supplied JMD/meta-introspector source
-- material.  Book and article citations calibrate terminology and theorem
-- boundaries; no citation imports proof or empirical authority.
------------------------------------------------------------------------

jmdMemeFormalismSource : Source.AttributedSource
jmdMemeFormalismSource =
  Source.mkNoDOISource
    "James Michael DuPont (JMD / meta-introspector)"
    "Meme-Theoretic Formalism of Intellectual Production"
    "JMD project material supplied with the SOLFUNMEME formalisation"
    "2026"
    "https://github.com/meta-introspector/monster"
    Source.communitySource
    "origin of the supplied meme-production, intellectual-shipping and typed-meme-compiler architecture"
    Source.publicAttribution

jmdSFMSource : Source.AttributedSource
jmdSFMSource =
  Source.mkNoDOISource
    "James Michael DuPont (JMD / meta-introspector)"
    "SOLFUNMEME as a Verified-Claim Presentation Layer"
    "JMD project material supplied with the SOLFUNMEME formalisation"
    "2026"
    "https://github.com/meta-introspector/Monster-LILA"
    Source.communitySource
    "origin of the supplied theorem-card, exact-view, diagnostic-view and visual-authority architecture"
    Source.publicAttribution

cantorSource : Source.AttributedSource
cantorSource =
  Source.mkNoDOISource
    "Georg Cantor"
    "Über eine elementare Frage der Mannigfaltigkeitslehre"
    "Jahresbericht der Deutschen Mathematiker-Vereinigung, volume 1"
    "1891"
    "https://gdz.sub.uni-goettingen.de/id/PPN37721857X_0001"
    Source.academicArticleSource
    "historical source for the diagonal non-surjectivity argument; the Agda theorem is independently kernel checked"
    Source.publicAttribution

copjecSource : Source.AttributedSource
copjecSource =
  Source.mkNoDOISource
    "Joan Copjec"
    "Read My Desire: Lacan Against the Historicists"
    "MIT Press"
    "1994"
    "https://mitpress.mit.edu/9780262531405/read-my-desire/"
    Source.academicBookSource
    "source calibration for the Kantian antinomy and Lacanian sexuation homology; no empirical person classification is imported"
    Source.publicAttribution

sublimeObjectSource : Source.AttributedSource
sublimeObjectSource =
  Source.mkNoDOISource
    "Slavoj Žižek"
    "The Sublime Object of Ideology"
    "Verso"
    "1989"
    "https://www.versobooks.com/products/1284-the-sublime-object-of-ideology"
    Source.academicBookSource
    "source calibration for fantasy, ideological closure, quilting and the sublime object"
    Source.publicAttribution

parallaxViewSource : Source.AttributedSource
parallaxViewSource =
  Source.mkNoDOISource
    "Slavoj Žižek"
    "The Parallax View"
    "The MIT Press"
    "2006"
    "https://mitpress.mit.edu/9780262240512/the-parallax-view/"
    Source.academicBookSource
    "source calibration for irreducible parallax gaps; topology-to-semantics remains a governed bridge"
    Source.publicAttribution

incontinenceSource : Source.AttributedSource
incontinenceSource =
  Source.mkNoDOISource
    "Slavoj Žižek"
    "Incontinence of the Void: Economico-Philosophical Spandrels"
    "The MIT Press"
    "2017"
    "https://mitpress.mit.edu/9780262537063/incontinence-of-the-void/"
    Source.academicBookSource
    "source calibration for constitutive excess and distinct surplus-value, enjoyment, knowledge and power channels"
    Source.publicAttribution

lenin2017Source : Source.AttributedSource
lenin2017Source =
  Source.mkNoDOISource
    "Slavoj Žižek (editor and essay author); V. I. Lenin (collected texts)"
    "Lenin 2017: Remembering, Repeating, and Working Through"
    "Verso"
    "2017"
    "https://www.versobooks.com/products/136-lenin-2017"
    Source.academicBookSource
    "source calibration for problem-preserving repetition and working-through rather than literal restoration"
    Source.publicAttribution

greenshieldsSource : Source.AttributedSource
greenshieldsSource =
  Source.mkDOISource
    "Will Greenshields"
    "Writing the Structures of the Subject: Lacan and Topology"
    "Palgrave Macmillan"
    "2017"
    "10.1007/978-3-319-47533-2"
    "https://link.springer.com/book/10.1007/978-3-319-47533-2"
    Source.academicBookSource
    "source calibration for Lacan's topological programme; the repository proves only a finite twisted-cover theorem"
    Source.publicAttribution

feigenbaumSource : Source.AttributedSource
feigenbaumSource =
  Source.mkDOISource
    "Mitchell J. Feigenbaum"
    "Quantitative Universality for a Class of Nonlinear Transformations"
    "Journal of Statistical Physics 19, 25-52"
    "1978"
    "10.1007/BF01020332"
    "https://link.springer.com/article/10.1007/BF01020332"
    Source.academicArticleSource
    "source calibration for period-doubling universality; 3.57 is a rounded chart value, not the exact accumulation constant"
    Source.publicAttribution

padicMemorySource : Source.AttributedSource
padicMemorySource =
  Source.mkDOISource
    "Sergio Albeverio, Andrei Khrennikov and Peter E. Kloeden"
    "Memory Retrieval as a p-Adic Dynamical System"
    "BioSystems 49(2), 105-115"
    "1999"
    "10.1016/S0303-2647(98)00035-5"
    "https://pubmed.ncbi.nlm.nih.gov/10203191/"
    Source.academicArticleSource
    "published precedent for a p-adic space-of-ideas model; not a mainstream biological encoding theorem"
    Source.publicAttribution

fearExtinctionSource : Source.AttributedSource
fearExtinctionSource =
  Source.mkDOISource
    "Bobae An, Jihye Kim, Kyungjoon Park and Sukwon Lee"
    "Amount of Fear Extinction Changes Its Underlying Mechanisms"
    "eLife 6:e25224"
    "2017"
    "10.7554/eLife.25224"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC5495569/"
    Source.academicArticleSource
    "calibrates the distinction between inhibitory-overlay and erasure-candidate learning modes"
    Source.publicAttribution

zizekPNFSources : List Source.AttributedSource
zizekPNFSources =
  jmdMemeFormalismSource
  ∷ jmdSFMSource
  ∷ cantorSource
  ∷ copjecSource
  ∷ sublimeObjectSource
  ∷ parallaxViewSource
  ∷ incontinenceSource
  ∷ lenin2017Source
  ∷ greenshieldsSource
  ∷ feigenbaumSource
  ∷ padicMemorySource
  ∷ fearExtinctionSource
  ∷ []

zizekPNFSourceAtlas : Source.AttributedSourceAtlas
zizekPNFSourceAtlas =
  Source.mkSourceAtlas
    "Zizek PNF, Cantor, SFM and learning source atlas"
    "DASHI.Reasoning.ZizekPNFSourceAtlas"
    zizekPNFSources
    "attribution and bounded formalisation relationships for the constructive, philosophical, topological, dynamical and learning layers"

zizekPNFSourceAtlasReceipt : GenericReceipt.GenericReceipt
zizekPNFSourceAtlasReceipt =
  Source.attributedSourceAtlasReceipt
    zizekPNFSourceAtlas
    "agda -i . DASHI/Reasoning/ZizekPNFSourceAtlas.agda"

zizekPNFSourceAtlasReceiptNonPromoting :
  GenericReceipt.promotesClaim zizekPNFSourceAtlasReceipt ≡ false
zizekPNFSourceAtlasReceiptNonPromoting = refl
