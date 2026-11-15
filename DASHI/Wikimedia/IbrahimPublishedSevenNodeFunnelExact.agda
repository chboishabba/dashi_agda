module DASHI.Wikimedia.IbrahimPublishedSevenNodeFunnelExact where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.WikipediaFirstLinkNetworkExact as FLN

------------------------------------------------------------------------
-- IBRAHIM-DANFORTH-DODDS, PUBLISHED SEVEN-NODE FIGURE REPLAY
--
-- Original source: Mark Ibrahim, Christopher M. Danforth,
-- Peter Sheridan Dodds, "Connecting every bit of knowledge:
-- The structure of Wikipedia's First Link Network",
-- Journal of Computational Science 19 (2017), 21-30,
-- DOI 10.1016/j.jocs.2016.12.001.
--
-- Concrete source fixture: 2016-11-20 author manuscript, Figures 2-4,
-- https://compstorylab.org/share/papers/ibrahim2016a/paper/
-- 2015-11-wikipedia-network.pdf
--
-- A -> B -> C -> A; D -> C; E -> C; F -> E; G -> E.
-- The published Fig. 2 visits and Fig. 3/4 funnels DIFFER.
-- The printed early pseudocode omits the first cycle-entry increment;
-- a later 2019 code correction makes it explicit. Both variants are
-- retained. This is DASHI's finite reconstruction, NOT an algorithm
-- parity claim for the unreproduced historical 4.7M-node Wikipedia run.
------------------------------------------------------------------------

methodSource : FLN.FirstLinkStudySource
methodSource = FLN.ibrahimDanforthDodds2017

data FigureNode : Set where
  a b c d e f g : FigureNode

figureFirstLink : FigureNode → FigureNode
figureFirstLink a = b
figureFirstLink b = c
figureFirstLink c = a
figureFirstLink d = c
figureFirstLink e = c
figureFirstLink f = e
figureFirstLink g = e

nodeEqual : FigureNode → FigureNode → Bool
nodeEqual a a = true
nodeEqual b b = true
nodeEqual c c = true
nodeEqual d d = true
nodeEqual e e = true
nodeEqual f f = true
nodeEqual g g = true
nodeEqual _ _ = false

memberNode : FigureNode → List FigureNode → Bool
memberNode target [] = false
memberNode target (node ∷ rest) with nodeEqual target node
... | true = true
... | false = memberNode target rest

isCycleVertex : FigureNode → Bool
isCycleVertex a = true
isCycleVertex b = true
isCycleVertex c = true
isCycleVertex d = false
isCycleVertex e = false
isCycleVertex f = false
isCycleVertex g = false

------------------------------------------------------------------------
-- Traversal visits: after taking the first edge, visit destinations
-- up to the first repetition (and include the repeating vertex).
-- Membership counts each destination once. For cycle starting nodes,
-- the entire cycle including the starting node is thereby visited.
------------------------------------------------------------------------

walkVisits : Nat → List FigureNode → FigureNode → List FigureNode
walkVisits zero seen current = []
walkVisits (suc fuel) seen current with memberNode current seen
... | true = current ∷ []
... | false =
  current ∷
  walkVisits fuel (current ∷ seen) (figureFirstLink current)

visitsFrom : FigureNode → List FigureNode
visitsFrom start =
  walkVisits 8 (start ∷ []) (figureFirstLink start)

------------------------------------------------------------------------
-- Traversal funnels: a path STARTING IN a cycle contributes zero.
-- For an outside start, count destinations up to the cycle boundary.
-- Published Fig. 3/4 includes first entry; older printed pseudocode
-- omits this entry. The two cases intentionally produce different C.
------------------------------------------------------------------------

data CycleEntryRule : Set where
  publishedFigureEntry unamendedPseudoNoEntry : CycleEntryRule

cycleBoundary : CycleEntryRule → FigureNode → List FigureNode
cycleBoundary publishedFigureEntry current = current ∷ []
cycleBoundary unamendedPseudoNoEntry current = []

walkFunnels :
  CycleEntryRule → Nat →
  List FigureNode → FigureNode → List FigureNode
walkFunnels policy zero seen current = []
walkFunnels policy (suc fuel) seen current with isCycleVertex current
... | true = cycleBoundary policy current
... | false with memberNode current seen
...   | true = []
...   | false =
  current ∷ walkFunnels policy fuel
    (current ∷ seen) (figureFirstLink current)

funnelsFrom : CycleEntryRule → FigureNode → List FigureNode
funnelsFrom policy start with isCycleVertex start
... | true = []
... | false =
  walkFunnels policy 8 (start ∷ []) (figureFirstLink start)

------------------------------------------------------------------------
-- Count inclusion across all seven starting articles, without
-- attributing the source-table computation to the new DASHI theorem.
------------------------------------------------------------------------

allStarts : List FigureNode
allStarts = a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ []

countContaining :
  (FigureNode → List FigureNode) →
  FigureNode → List FigureNode → Nat
countContaining path target [] = 0
countContaining path target (start ∷ rest) with
  memberNode target (path start)
... | true = suc (countContaining path target rest)
... | false = countContaining path target rest

visitsCount : FigureNode → Nat
visitsCount node = countContaining visitsFrom node allStarts

funnelCount : CycleEntryRule → FigureNode → Nat
funnelCount rule node =
  countContaining (funnelsFrom rule) node allStarts

------------------------------------------------------------------------
-- Source's original FIGURE VALUES: all are actual reductions
-- of the deterministic first-link fixture and path algorithm.
------------------------------------------------------------------------

figureTwoA : visitsCount a ≡ 7
figureTwoA = refl

figureTwoB : visitsCount b ≡ 7
figureTwoB = refl

figureTwoC : visitsCount c ≡ 7
figureTwoC = refl

figureTwoD : visitsCount d ≡ 0
figureTwoD = refl

figureTwoE : visitsCount e ≡ 2
figureTwoE = refl

figureTwoF : visitsCount f ≡ 0
figureTwoF = refl

figureTwoG : visitsCount g ≡ 0
figureTwoG = refl

figureFourA : funnelCount publishedFigureEntry a ≡ 0
figureFourA = refl

figureFourB : funnelCount publishedFigureEntry b ≡ 0
figureFourB = refl

figureFourC : funnelCount publishedFigureEntry c ≡ 4
figureFourC = refl

figureFourD : funnelCount publishedFigureEntry d ≡ 0
figureFourD = refl

figureFourE : funnelCount publishedFigureEntry e ≡ 2
figureFourE = refl

figureFourF : funnelCount publishedFigureEntry f ≡ 0
figureFourF = refl

figureFourG : funnelCount publishedFigureEntry g ≡ 0
figureFourG = refl

unamendedPseudocodeOmittedC :
  funnelCount unamendedPseudoNoEntry c ≡ 0
unamendedPseudocodeOmittedC = refl

publishedCycleEntryDiffersFromUnamendedPseudocode :
  funnelCount publishedFigureEntry c ≡
  funnelCount unamendedPseudoNoEntry c → ⊥
publishedCycleEntryDiffersFromUnamendedPseudocode ()

------------------------------------------------------------------------
-- Attribution and proof-authority boundary.
------------------------------------------------------------------------

data FigureImpliesFullCorpusReplay : Set where
data LaterCodeRewritesPublishedPseudocode : Set where
data CycleFunnelRankingProvesCulturalCause : Set where

figureIsNotFullCorpusReplay : FigureImpliesFullCorpusReplay → ⊥
figureIsNotFullCorpusReplay ()

laterCodeDoesNotRetroactivelyRewriteSource :
  LaterCodeRewritesPublishedPseudocode → ⊥
laterCodeDoesNotRetroactivelyRewriteSource ()

funnelRankDoesNotProveCulture :
  CycleFunnelRankingProvesCulturalCause → ⊥
funnelRankDoesNotProveCulture ()
