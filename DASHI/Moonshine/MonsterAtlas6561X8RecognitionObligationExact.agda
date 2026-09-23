module DASHI.Moonshine.MonsterAtlas6561X8RecognitionObligationExact where

------------------------------------------------------------------------
-- MONSTER 3-LOCAL 6561-POINT ACTION: EXACT RECOGNITION OBLIGATION
--
-- External fact/source status:
-- ATLAS lists a transitive but imprimitive permutation representation on
-- 6561 points of the proper image
--
--   3^(2+6+6):(L3(3) x SD16)
--
-- associated to the Monster maximal subgroup
--
--   3^(3+2+6+6):(L3(3) x SD16).
--
-- This module does NOT fabricate the permutation generators or their block
-- system.  Instead it states exactly what must be acquired/computed before
-- DASHI's X8 = X6 x T^2 carrier may be recognised as that action.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Moonshine.Base369MonsterThreeLocalEightToSixPlusTwoCarrierBidiExact as X8
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- 1. Source receipt.
------------------------------------------------------------------------

atlas6561Source : Attribution.AttributedSource
atlas6561Source = Attribution.mkNoDOISource
  "ATLAS of Finite Group Representations contributors"
  "Permutation representation on 6561 points for the proper image 3^(2+6+6):(L3(3) x SD16)"
  "ATLAS of Finite Group Representations"
  "retrieved 2026-09-23"
  "https://brauer.maths.qmul.ac.uk/Atlas/v3/permrep/Mmax15q1G0-p6561B0"
  (Attribution.namedSourceKind "finite-group database record")
  "source states degree 6561 and marks the action transitive but imprimitive; it does not by itself identify a 9 x 729 block chart or DASHI X8"
  Attribution.publicAttribution

atlas6561Attribution =
  Snowball.canonicalSourceRoleSnowballReceipt atlas6561Source

------------------------------------------------------------------------
-- 2. Neutral finite carriers suggested by the arithmetic only.
------------------------------------------------------------------------

AtlasPoint6561 : Set
AtlasPoint6561 = Fin 6561

CandidateBlock9 : Set
CandidateBlock9 = Fin 9

CandidateWithinBlock729 : Set
CandidateWithinBlock729 = Fin 729

nineTimes729Is6561 : 9 * 729 ≡ 6561
nineTimes729Is6561 = refl

threeSquaredTimesThreeSixthIsThreeEighth :
  (3 * 3) * 729 ≡ 6561
threeSquaredTimesThreeSixthIsThreeEighth = refl

------------------------------------------------------------------------
-- 3. The actual permutation data must be supplied, not inferred.
------------------------------------------------------------------------

record Atlas6561PermutationData : Set₁ where
  field
    Generator : Set
    act : Generator → AtlasPoint6561 → AtlasPoint6561

    sourceIdentifier : String
    firstGeneratorFile : String
    secondGeneratorFile : String

    generatorFilesAcquired : Bool
    actionDecodedFromGeneratorFiles : Bool

open Atlas6561PermutationData public

------------------------------------------------------------------------
-- 4. Candidate imprimitive 9 x 729 chart.
--
-- ATLAS says "imprimitive", but not in the cited page that the canonical
-- blocks have count 9 and size 729.  Therefore both directions and action
-- compatibility are explicit proof obligations.
------------------------------------------------------------------------

record NineBy729BlockRecognition
    (P : Atlas6561PermutationData) : Set₁ where
  field
    encode :
      AtlasPoint6561 →
      CandidateBlock9 × CandidateWithinBlock729

    decode :
      CandidateBlock9 × CandidateWithinBlock729 →
      AtlasPoint6561

    decodeEncode :
      (p : AtlasPoint6561) →
      decode (encode p) ≡ p

    encodeDecode :
      (q : CandidateBlock9 × CandidateWithinBlock729) →
      encode (decode q) ≡ q

    blockAct :
      Generator P →
      CandidateBlock9 →
      CandidateBlock9

    withinBlockAct :
      Generator P →
      CandidateBlock9 →
      CandidateWithinBlock729 →
      CandidateWithinBlock729

    actionIntertwines :
      (g : Generator P) →
      (p : AtlasPoint6561) →
      encode (act P g p)
      ≡
      let q = encode p
      in
      blockAct g (proj₁ q)
      ,
      withinBlockAct g (proj₁ q) (proj₂ q)

open NineBy729BlockRecognition public

------------------------------------------------------------------------
-- 5. Actual equivariant recognition of DASHI X8.
------------------------------------------------------------------------

record Atlas6561X8Recognition
    (P : Atlas6561PermutationData) : Set₁ where
  field
    toX8 : AtlasPoint6561 → X8.X8
    fromX8 : X8.X8 → AtlasPoint6561

    fromAfterTo :
      (p : AtlasPoint6561) →
      fromX8 (toX8 p) ≡ p

    toAfterFrom :
      (x : X8.X8) →
      toX8 (fromX8 x) ≡ x

    x8Act :
      Generator P →
      X8.X8 →
      X8.X8

    sameAction :
      (g : Generator P) →
      (p : AtlasPoint6561) →
      toX8 (act P g p)
      ≡ x8Act g (toX8 p)

open Atlas6561X8Recognition public

------------------------------------------------------------------------
-- 6. Strong recognition package: action + blocks + X8.
------------------------------------------------------------------------

record Atlas6561FullRecognition : Set₁ where
  field
    permutationData : Atlas6561PermutationData
    blockRecognition : NineBy729BlockRecognition permutationData
    x8Recognition : Atlas6561X8Recognition permutationData

open Atlas6561FullRecognition public

------------------------------------------------------------------------
-- 7. Explicit fail-closed acquisition frontier.
------------------------------------------------------------------------

data Atlas6561ActionAlreadyRecognisedAsX8 : Set where
data AtlasImprimitiveBlocksAlreadyProvedNineBy729 : Set where
data ExponentTwoPlusSixAloneCreatesBlockSystem : Set where

atlasActionNotRecognisedFromCardinality :
  Atlas6561ActionAlreadyRecognisedAsX8 → ⊥
atlasActionNotRecognisedFromCardinality ()

imprimitiveDoesNotYetMeanNineBy729 :
  AtlasImprimitiveBlocksAlreadyProvedNineBy729 → ⊥
imprimitiveDoesNotYetMeanNineBy729 ()

twoPlusSixDoesNotCreateBlocksByItself :
  ExponentTwoPlusSixAloneCreatesBlockSystem → ⊥
twoPlusSixDoesNotCreateBlocksByItself ()

record Atlas6561RecognitionFrontier : Set where
  constructor atlas-6561-recognition-frontier
  field
    sourceDegree6561Recorded : Bool
    sourceTransitiveRecorded : Bool
    sourceImprimitiveRecorded : Bool
    candidateNineBy729ArithmeticPaid : Bool
    generatorFileIdentifiersLocated : Bool

    generatorBytesAcquiredHere : Bool
    actualPermutationActionDecodedHere : Bool
    actualBlockSystemComputedHere : Bool
    canonicalNineBy729BlockChartProvedHere : Bool
    x8EquivariantRecognitionInhabitedHere : Bool

canonicalAtlas6561RecognitionFrontier :
  Atlas6561RecognitionFrontier
canonicalAtlas6561RecognitionFrontier =
  atlas-6561-recognition-frontier
    true true true true true
    false false false false false
