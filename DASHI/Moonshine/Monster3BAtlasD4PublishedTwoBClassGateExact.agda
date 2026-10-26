module DASHI.Moonshine.Monster3BAtlasD4PublishedTwoBClassGateExact where

------------------------------------------------------------------------
-- ORIGINAL EXTERNAL SOURCES, not new repository discoveries:
--
-- (1) S. P. Norton and R. A. Wilson,
--   "Anatomy of the Monster: II", Proc. LMS 84 (2002), 581--598,
--   DOI 10.1112/S0024611502013357.
--   The central involution -1_A of 2.Suz in the Monster 3B centralizer
--   belongs to the Monster conjugacy class 2B.
--   Journal DOI/source record is primary; body sentence cross-read in
--   an HTML reproduction (not a second independent source root).
--
-- (2) R. W. Barraclough and R. A. Wilson,
--   "Conjugacy Class Representatives in the Monster Group",
--   LMS J. Comput. Math. 8 (2005), 205--216,
--   DOI 10.1112/S1461157000000966.
--   Original Table 2 gives Monster 2A as a square of Monster 4B.
--
-- (3) R. W. Barraclough and R. A. Wilson (2007),
--   DOI 10.1112/S1461157000001352, section 3.1 explicitly uses
--   2.Suz:2 ATLAS dimension12 standard generators C2,D2, obtained
--   from the 6.Suz:2 source standard generators via C6->C2,D6->D2.
--
-- ORIGINAL MATRIX BYTES: ATLAS/AtlasRep 2.Suz:2 GF3, SHA256 manifest
-- and exact source-word D4 witness in existing DASHI PR #1098.
-- In that source D4 r^2=-I12, the unique central involution of 2.Suz.
--
-- The conditional source-power/map inference is trivial finite logic:
-- if r^2 has Monster class 2B, r cannot have Monster class 4B
-- because that square has Monster class 2A, distinct from 2B.
-- Agda only formalizes this two-class discrimination from explicitly
-- attributed SOURCE INPUTS.  It does NOT kernel-prove the Monster class
-- fusion, source quotient embeddings, or the actual induced 729x90 Hom.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

nortonWilson2002 : Attribution.AttributedSource
nortonWilson2002 = Attribution.mkDOISource
  "S. P. Norton; R. A. Wilson"
  "Anatomy of the Monster: II"
  "Proceedings of the London Mathematical Society 84, 581-598"
  "2002"
  "10.1112/S0024611502013357"
  "https://doi.org/10.1112/S0024611502013357"
  Attribution.academicArticleSource
  "primary published central 2.Suz involution -1_A is Monster class 2B"
  Attribution.publicAttribution

barracloughWilson2005 : Attribution.AttributedSource
barracloughWilson2005 = Attribution.mkDOISource
  "R. W. Barraclough; R. A. Wilson"
  "Conjugacy Class Representatives in the Monster Group"
  "LMS Journal of Computation and Mathematics 8, 205-216"
  "2005"
  "10.1112/S1461157000000966"
  "https://doi.org/10.1112/S1461157000000966"
  Attribution.academicArticleSource
  "primary published Monster Table 2: class 4B squares into 2A"
  Attribution.publicAttribution

barracloughWilson2007 : Attribution.AttributedSource
barracloughWilson2007 = Attribution.mkDOISource
  "R. W. Barraclough; R. A. Wilson"
  "The Character Table of a Maximal Subgroup of the Monster"
  "LMS Journal of Computation and Mathematics 10, 161-175"
  "2007"
  "10.1112/S1461157000001352"
  "https://doi.org/10.1112/S1461157000001352"
  Attribution.academicArticleSource
  "section 3.1 standard-generator 6.Suz:2 to 2.Suz:2 module projection"
  Attribution.publicAttribution

nortonWilsonSourceRole =
  Snowball.canonicalSourceRoleSnowballReceipt nortonWilson2002
barracloughWilson2005SourceRole =
  Snowball.canonicalSourceRoleSnowballReceipt barracloughWilson2005
barracloughWilson2007SourceRole =
  Snowball.canonicalSourceRoleSnowballReceipt barracloughWilson2007

data InvolutionMonsterClass : Set where
  twoA : InvolutionMonsterClass
  twoB : InvolutionMonsterClass

data FourMonsterClass : Set where
  fourB : FourMonsterClass
  otherOrderFourSourceClass : FourMonsterClass

-- SOURCE-ATTRIBUTED values, not computed source-group proof inhabitants.
publishedFourBSquareClass : InvolutionMonsterClass
publishedFourBSquareClass = twoA

publishedSuzukiCentralMinusOneFusion : InvolutionMonsterClass
publishedSuzukiCentralMinusOneFusion = twoB

-- This is the exact two-class contradiction.  The identity between the
-- source matrix r²=-I and Norton-Wilson's -1_A is an external group-word
-- acquisition premise, checked for the ATLAS source representation and
-- transported to the selected Monster quotient by an additional source map.
fourBImpossibleForSourceD4UnderPublishedFusion :
  publishedFourBSquareClass
  ≡ publishedSuzukiCentralMinusOneFusion → ⊥
fourBImpossibleForSourceD4UnderPublishedFusion ()

record PublishedSourceBoundary : Set where
  constructor published-source-boundary
  field
    originalNW2002SourceRecognized : Bool
    originalBW2005PowerMapSourceRecognized : Bool
    originalBW2007StandardGeneratorProjectionRecognized : Bool
    sourceATLASD4HalfTurnIsNegativeIdentityLocallyChecked : Bool
    publishedTwoBVersusTwoASourceIncompatibilityTyped : Bool
    sourceSelectedMonsterDiagonalQuotientElementWordAcquired : Bool
    completeMonsterOrderFourClassDetermined : Bool
    selected6SuzDegree78FullCharacterGAPReceipt : Bool
    sourceActualWZetaHomActionKernelChecked : Bool
    thisModuleAgdaKernelChecked : Bool

currentBoundary : PublishedSourceBoundary
currentBoundary = published-source-boundary
  true true true true true false false false false false
