module DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.List.Base using (length)
open import Data.Nat.Properties using (suc-injective)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanFourDimensionalHaloOverlapExact using
  (lengthMap; lengthAppend; lengthCartesian; lengthAllCyclicIndices)
open import DASHI.Physics.YangMills.BalabanDyadicQuantitativeRegionExact using
  (_<N_; ltBool; ltBoolSound)

------------------------------------------------------------------------
-- Exact finite entropy carrier for rooted four-dimensional polymer traces.
------------------------------------------------------------------------

SignedAxis4 : Set
SignedAxis4 = Product Axis4 Bool

boolEnumeration : List Bool
boolEnumeration = false ∷ true ∷ []

boolEnumerationComplete : ∀ value → value ∈ boolEnumeration
boolEnumerationComplete false = here
boolEnumerationComplete true = there here

signedDirectionEnumeration : List SignedAxis4
signedDirectionEnumeration =
  cartesian (allCyclicIndices four) boolEnumeration

signedDirectionEnumerationComplete : ∀ direction →
  direction ∈ signedDirectionEnumeration
signedDirectionEnumerationComplete (pair axis orientation) =
  cartesianMembership
    (allCyclicIndicesComplete axis)
    (boolEnumerationComplete orientation)

two eight : Nat
two = suc (suc zero)
eight = four * two

signedDirectionEnumerationLength :
  length signedDirectionEnumeration ≡ eight
signedDirectionEnumerationLength
  rewrite lengthCartesian (allCyclicIndices four) boolEnumeration
  | lengthAllCyclicIndices four = refl

prependAll : ∀ {A : Set} → List A → List (List A) → List (List A)
prependAll [] words = []
prependAll (direction ∷ directions) words =
  map (λ word → direction ∷ word) words
  ++ prependAll directions words

prependAllLength : ∀ {A : Set} (directions : List A) words →
  length (prependAll directions words)
  ≡ length directions * length words
prependAllLength [] words = refl
prependAllLength (direction ∷ directions) words
  rewrite lengthAppend
    (map (λ word → direction ∷ word) words)
    (prependAll directions words)
  | lengthMap (λ word → direction ∷ word) words
  | prependAllLength directions words = refl

prependAllMembership :
  ∀ {A : Set} {direction : A} {directions word words} →
  direction ∈ directions →
  word ∈ words →
  (direction ∷ word) ∈ prependAll directions words
prependAllMembership {direction = direction} here wordMembership =
  appendMembershipLeft
    (mapMembership (λ word → direction ∷ word) wordMembership)
prependAllMembership (there directionMembership) wordMembership =
  appendMembershipRight
    (prependAllMembership directionMembership wordMembership)

allSignedWords : Nat → List (List SignedAxis4)
allSignedWords zero = [] ∷ []
allSignedWords (suc depth) =
  prependAll signedDirectionEnumeration (allSignedWords depth)

pow8 : Nat → Nat
pow8 zero = suc zero
pow8 (suc depth) = eight * pow8 depth

allSignedWordsLength : ∀ depth →
  length (allSignedWords depth) ≡ pow8 depth
allSignedWordsLength zero = refl
allSignedWordsLength (suc depth)
  rewrite prependAllLength signedDirectionEnumeration (allSignedWords depth)
  | signedDirectionEnumerationLength
  | allSignedWordsLength depth = refl

allSignedWordsComplete : ∀ {depth} word →
  length word ≡ depth →
  word ∈ allSignedWords depth
allSignedWordsComplete {zero} [] refl = here
allSignedWordsComplete {zero} (direction ∷ word) ()
allSignedWordsComplete {suc depth} [] ()
allSignedWordsComplete {suc depth} (direction ∷ word) lengthProof =
  prependAllMembership
    (signedDirectionEnumerationComplete direction)
    (allSignedWordsComplete word (suc-injective lengthProof))

record RootedTrace (Root : Set) (depth : Nat) : Set where
  constructor rootedTrace
  field
    root : Root
    directions : List SignedAxis4
    directionsLength : length directions ≡ depth

open RootedTrace public

rootedTraceWordEnumerated :
  ∀ {Root depth} (trace : RootedTrace Root depth) →
  directions trace ∈ allSignedWords depth
rootedTraceWordEnumerated trace =
  allSignedWordsComplete (directions trace) (directionsLength trace)

------------------------------------------------------------------------
-- A dyadic suppression of 1/16 per traversal step beats branching factor 8.
------------------------------------------------------------------------

traceSuppressionDenominator : Nat
traceSuppressionDenominator = 16

traceBranchingBelowSuppressionComputation :
  ltBool eight traceSuppressionDenominator ≡ true
traceBranchingBelowSuppressionComputation = refl

traceBranchingBelowSuppression :
  eight <N traceSuppressionDenominator
traceBranchingBelowSuppression =
  ltBoolSound eight traceSuppressionDenominator
    traceBranchingBelowSuppressionComputation

record PhysicalPolymerTraceEncoding (Polymer : Set) : Set₁ where
  field
    polymerSize : Polymer → Nat
    canonicalTraceWord : Polymer → List SignedAxis4
    canonicalTraceLength : ∀ polymer →
      length (canonicalTraceWord polymer) ≡ polymerSize polymer

    traceEncodingInjective : ∀ {left right} →
      canonicalTraceWord left ≡ canonicalTraceWord right →
      left ≡ right

open PhysicalPolymerTraceEncoding public

canonicalPolymerTraceEnumerated :
  ∀ {Polymer}
    (encoding : PhysicalPolymerTraceEncoding Polymer)
    polymer →
  canonicalTraceWord encoding polymer
  ∈ allSignedWords (polymerSize encoding polymer)
canonicalPolymerTraceEnumerated encoding polymer =
  allSignedWordsComplete
    (canonicalTraceWord encoding polymer)
    (canonicalTraceLength encoding polymer)

rootedTraceWordEnumerationLevel : ProofLevel
rootedTraceWordEnumerationLevel = machineChecked

rootedTraceEntropyCountLevel : ProofLevel
rootedTraceEntropyCountLevel = machineChecked

traceSuppressionBeatsBranchingLevel : ProofLevel
traceSuppressionBeatsBranchingLevel = computed

physicalPolymerTraceEncodingLevel : ProofLevel
physicalPolymerTraceEncodingLevel = conditional

physicalKoteckyPreissGeometricSumLevel : ProofLevel
physicalKoteckyPreissGeometricSumLevel = conditional
