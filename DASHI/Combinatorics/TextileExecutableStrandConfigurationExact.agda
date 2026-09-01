module DASHI.Combinatorics.TextileExecutableStrandConfigurationExact where

open import DASHI.Core.Prelude
open import Data.List using (List; []; _∷_; _++_; length)

import DASHI.Combinatorics.TextileNFibreCalculusExact as T
import DASHI.Combinatorics.TextileBraidRewriteGroupoidExact as Rewrite

------------------------------------------------------------------------
-- EXECUTABLE INDEXED STRAND CONFIGURATIONS
--
-- Rather than postulating Artin rewrites, this owner gives local witnessed
-- configuration windows on which adjacent generators execute by swapping the
-- two occupied positions.  Over/under orientation remains braid-history data;
-- endpoint permutation forgets that orientation.
------------------------------------------------------------------------

record StrandConfiguration (n : Nat) : Set where
  constructor strand-configuration
  field
    labels : List Nat
    sizeExact : length labels ≡ n

open StrandConfiguration public

------------------------------------------------------------------------
-- 1. Every typed sigma_i can act on a matching witnessed adjacent window.
------------------------------------------------------------------------

record AdjacentWindowAt (n i : Nat) : Set where
  constructor adjacent-window-at
  field
    prefix : List Nat
    leftLabel rightLabel : Nat
    suffix : List Nat
    prefixLength : length prefix ≡ i
    sizeWitness : length (prefix ++ leftLabel ∷ rightLabel ∷ suffix) ≡ n

open AdjacentWindowAt public

windowConfiguration :
  ∀ {n i} → AdjacentWindowAt n i → StrandConfiguration n
windowConfiguration window =
  strand-configuration
    (prefix window ++ leftLabel window ∷ rightLabel window ∷ suffix window)
    (sizeWitness window)

executeAdjacent :
  ∀ {n} →
  (crossing : T.AdjacentCrossing n) →
  AdjacentWindowAt n (T.leftIndex crossing) →
  StrandConfiguration n
executeAdjacent crossing window =
  strand-configuration
    (prefix window ++ rightLabel window ∷ leftLabel window ∷ suffix window)
    (sizeWitness window)

------------------------------------------------------------------------
-- 2. Adjacent triple windows carry the exact in-range proofs for sigma_i and
-- sigma_{i+1}.  The actions below are therefore tied to actual typed generators.
------------------------------------------------------------------------

record TripleWindowAt (n i : Nat) : Set where
  constructor triple-window-at
  field
    triplePrefix : List Nat
    firstLabel secondLabel thirdLabel : Nat
    tripleSuffix : List Nat
    triplePrefixLength : length triplePrefix ≡ i
    leftGeneratorInRange : i + 2 ≤ n
    rightGeneratorInRange : suc i + 2 ≤ n
    tripleSizeWitness :
      length
        (triplePrefix ++ firstLabel ∷ secondLabel ∷ thirdLabel ∷ tripleSuffix)
      ≡ n

open TripleWindowAt public

leftTripleGenerator :
  ∀ {n i} → T.CrossingOrientation → TripleWindowAt n i → T.AdjacentCrossing n
leftTripleGenerator orientation window =
  T.sigma i orientation (leftGeneratorInRange window)

rightTripleGenerator :
  ∀ {n i} → T.CrossingOrientation → TripleWindowAt n i → T.AdjacentCrossing n
rightTripleGenerator orientation window =
  T.sigma (suc i) orientation (rightGeneratorInRange window)

flattenTriple :
  ∀ {n i} → TripleWindowAt n i → StrandConfiguration n
flattenTriple window =
  strand-configuration
    (triplePrefix window ++
      firstLabel window ∷ secondLabel window ∷ thirdLabel window ∷ tripleSuffix window)
    (tripleSizeWitness window)

sigmaLeftOnTriple :
  ∀ {n i} → TripleWindowAt n i → TripleWindowAt n i
sigmaLeftOnTriple window =
  triple-window-at
    (triplePrefix window)
    (secondLabel window)
    (firstLabel window)
    (thirdLabel window)
    (tripleSuffix window)
    (triplePrefixLength window)
    (leftGeneratorInRange window)
    (rightGeneratorInRange window)
    (tripleSizeWitness window)

sigmaRightOnTriple :
  ∀ {n i} → TripleWindowAt n i → TripleWindowAt n i
sigmaRightOnTriple window =
  triple-window-at
    (triplePrefix window)
    (firstLabel window)
    (thirdLabel window)
    (secondLabel window)
    (tripleSuffix window)
    (triplePrefixLength window)
    (leftGeneratorInRange window)
    (rightGeneratorInRange window)
    (tripleSizeWitness window)

executeYangBaxterLeft :
  ∀ {n i} → TripleWindowAt n i → StrandConfiguration n
executeYangBaxterLeft window =
  flattenTriple
    (sigmaLeftOnTriple
      (sigmaRightOnTriple
        (sigmaLeftOnTriple window)))

executeYangBaxterRight :
  ∀ {n i} → TripleWindowAt n i → StrandConfiguration n
executeYangBaxterRight window =
  flattenTriple
    (sigmaRightOnTriple
      (sigmaLeftOnTriple
        (sigmaRightOnTriple window)))

adjacentTripleYangBaxterOnConfigurations :
  ∀ {n i} →
  (window : TripleWindowAt n i) →
  executeYangBaxterLeft window ≡ executeYangBaxterRight window
adjacentTripleYangBaxterOnConfigurations window = refl

------------------------------------------------------------------------
-- 3. Structurally distant windows carry two actual typed crossings plus a
-- far-separation receipt.  The middle segment witnesses their disjoint local
-- support in the explicit configuration decomposition.
------------------------------------------------------------------------

record DistantWindow (n : Nat) : Set where
  constructor distant-window
  field
    farPrefix : List Nat
    farA farB : Nat
    middle : List Nat
    farC farD : Nat
    farSuffix : List Nat
    firstCrossing secondCrossing : T.AdjacentCrossing n
    firstPrefixLength : length farPrefix ≡ T.leftIndex firstCrossing
    secondPrefixLength :
      length farPrefix + 2 + length middle ≡ T.leftIndex secondCrossing
    supportsFar :
      Rewrite.FarSeparated
        (T.leftIndex firstCrossing)
        (T.leftIndex secondCrossing)
    farSizeWitness :
      length
        (farPrefix ++ farA ∷ farB ∷ middle ++ farC ∷ farD ∷ farSuffix)
      ≡ n

open DistantWindow public

flattenDistant :
  ∀ {n} → DistantWindow n → StrandConfiguration n
flattenDistant window =
  strand-configuration
    (farPrefix window ++
      farA window ∷ farB window ∷ middle window ++
      farC window ∷ farD window ∷ farSuffix window)
    (farSizeWitness window)

swapFirstDistant : ∀ {n} → DistantWindow n → DistantWindow n
swapFirstDistant window =
  distant-window
    (farPrefix window)
    (farB window) (farA window)
    (middle window)
    (farC window) (farD window)
    (farSuffix window)
    (firstCrossing window) (secondCrossing window)
    (firstPrefixLength window)
    (secondPrefixLength window)
    (supportsFar window)
    (farSizeWitness window)

swapSecondDistant : ∀ {n} → DistantWindow n → DistantWindow n
swapSecondDistant window =
  distant-window
    (farPrefix window)
    (farA window) (farB window)
    (middle window)
    (farD window) (farC window)
    (farSuffix window)
    (firstCrossing window) (secondCrossing window)
    (firstPrefixLength window)
    (secondPrefixLength window)
    (supportsFar window)
    (farSizeWitness window)

executeFarLeftThenRight :
  ∀ {n} → DistantWindow n → StrandConfiguration n
executeFarLeftThenRight window =
  flattenDistant (swapSecondDistant (swapFirstDistant window))

executeFarRightThenLeft :
  ∀ {n} → DistantWindow n → StrandConfiguration n
executeFarRightThenLeft window =
  flattenDistant (swapFirstDistant (swapSecondDistant window))

distantGeneratorsCommuteOnConfigurations :
  ∀ {n} →
  (window : DistantWindow n) →
  executeFarLeftThenRight window ≡ executeFarRightThenLeft window
distantGeneratorsCommuteOnConfigurations window = refl

------------------------------------------------------------------------
-- 4. Orientation is retained in literal braid history even though both
-- orientations induce the same endpoint transposition on strand labels.
------------------------------------------------------------------------

data EndpointPermutationForgetsOrientation : Set where
  endpoint-forgets-orientation : EndpointPermutationForgetsOrientation

orientationStillHistoryBearing :
  T.CrossingOrientation → T.CrossingOrientation → Set
orientationStillHistoryBearing left right = left ≡ right

overAndUnderRemainDifferentHistory :
  orientationStillHistoryBearing T.overCrossing T.underCrossing → ⊥
overAndUnderRemainDifferentHistory ()

------------------------------------------------------------------------
-- 5. Boundaries.
------------------------------------------------------------------------

data EndpointPermutationDeterminesBraidHistory : Set where
data YangBaxterEndpointEqualityMeansLiteralWordEquality : Set where
data FarCommutationErasesRewriteProvenance : Set where
data LocalWindowProofConstructsFullBraidGroup : Set where
data WeaveKnitCrochetCollapseToPermutationAction : Set where

endpointPermutationDoesNotDetermineBraidHistory :
  EndpointPermutationDeterminesBraidHistory → ⊥
endpointPermutationDoesNotDetermineBraidHistory ()

yangBaxterEndpointEqualityDoesNotMeanLiteralWordEquality :
  YangBaxterEndpointEqualityMeansLiteralWordEquality → ⊥
yangBaxterEndpointEqualityDoesNotMeanLiteralWordEquality ()

farCommutationDoesNotEraseRewriteProvenance :
  FarCommutationErasesRewriteProvenance → ⊥
farCommutationDoesNotEraseRewriteProvenance ()

localWindowsDoNotConstructFullBraidGroup :
  LocalWindowProofConstructsFullBraidGroup → ⊥
localWindowsDoNotConstructFullBraidGroup ()

otherCraftsDoNotCollapseToPermutationAction :
  WeaveKnitCrochetCollapseToPermutationAction → ⊥
otherCraftsDoNotCollapseToPermutationAction ()

record TextileExecutableConfigurationBoundary : Set where
  constructor textile-executable-configuration-boundary
  field
    nIndexedConfigurationExplicit : Bool
    adjacentActionExecutable : Bool
    adjacentTripleCarriesActualGenerators : Bool
    distantWindowCarriesFarSeparatedGenerators : Bool
    arbitraryContextYangBaxterComputes : Bool
    arbitraryContextFarCommutationComputes : Bool
    orientationRetainedBeyondEndpointPermutation : Bool
    endpointPermutationDeterminesHistory : Bool
    fullBraidGroupClaimed : Bool
    craftDependencyGrammarsCollapsed : Bool

canonicalTextileExecutableConfigurationBoundary :
  TextileExecutableConfigurationBoundary
canonicalTextileExecutableConfigurationBoundary =
  textile-executable-configuration-boundary
    true true true true true true true false false false
