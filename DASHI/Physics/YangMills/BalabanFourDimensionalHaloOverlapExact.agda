module DASHI.Physics.YangMills.BalabanFourDimensionalHaloOverlapExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.List.Base using (length)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier

------------------------------------------------------------------------
-- Exact overlap count for a regular four-dimensional translated halo cover.
--
-- At a fixed site, a containing translated halo is parameterised by one
-- relative origin offset in each coordinate.  If the one-dimensional halo
-- window contains w offsets, the literal fourfold offset enumeration has
-- cardinality w^4.  This module proves that count from the repository's actual
-- CyclicIndex enumeration and cartesian-product implementation.
------------------------------------------------------------------------

lengthMap :
  ∀ {A B : Set} (f : A → B) (values : List A) →
  length (map f values) ≡ length values
lengthMap f [] = refl
lengthMap f (value ∷ values) = cong suc (lengthMap f values)

lengthAppend :
  ∀ {A : Set} (left right : List A) →
  length (left ++ right) ≡ length left + length right
lengthAppend [] right = refl
lengthAppend (value ∷ left) right =
  cong suc (lengthAppend left right)

lengthCartesian :
  ∀ {A B : Set} (left : List A) (right : List B) →
  length (cartesian left right) ≡ length left * length right
lengthCartesian [] right = refl
lengthCartesian (value ∷ left) right
  rewrite lengthAppend
    (map (λ item → pair value item) right)
    (cartesian left right)
  | lengthMap (λ item → pair value item) right
  | lengthCartesian left right = refl

lengthAllCyclicIndices : ∀ width →
  length (allCyclicIndices width) ≡ width
lengthAllCyclicIndices zero = refl
lengthAllCyclicIndices (suc width)
  rewrite lengthMap sucᵢ (allCyclicIndices width)
  | lengthAllCyclicIndices width = refl

squareCount : Nat → Nat
squareCount width = width * width

fourthPowerCount : Nat → Nat
fourthPowerCount width = squareCount width * squareCount width

haloOffset4 : Nat → Set
haloOffset4 width = Fourfold (CyclicIndex width)

haloOffsetEnumeration : (width : Nat) → List (haloOffset4 width)
haloOffsetEnumeration width =
  elements (periodicTorus4Finite width)

pairOffsetLength : ∀ width →
  length
    (cartesian
      (allCyclicIndices width)
      (allCyclicIndices width))
  ≡ squareCount width
pairOffsetLength width
  rewrite lengthCartesian
    (allCyclicIndices width)
    (allCyclicIndices width)
  | lengthAllCyclicIndices width = refl

haloOffsetEnumerationLength : ∀ width →
  length (haloOffsetEnumeration width) ≡ fourthPowerCount width
haloOffsetEnumerationLength width
  rewrite lengthCartesian
    (cartesian
      (allCyclicIndices width)
      (allCyclicIndices width))
    (cartesian
      (allCyclicIndices width)
      (allCyclicIndices width))
  | pairOffsetLength width = refl

record RegularTranslatedHaloCover : Set where
  constructor regularTranslatedHaloCover
  field
    blockSide haloWidth : Nat

open RegularTranslatedHaloCover public

haloAxisWidth : RegularTranslatedHaloCover → Nat
haloAxisWidth cover =
  blockSide cover + (haloWidth cover + haloWidth cover)

localContainingHaloOffsets :
  RegularTranslatedHaloCover → Set
localContainingHaloOffsets cover = haloOffset4 (haloAxisWidth cover)

localContainingHaloOffsetEnumeration :
  (cover : RegularTranslatedHaloCover) →
  List (localContainingHaloOffsets cover)
localContainingHaloOffsetEnumeration cover =
  haloOffsetEnumeration (haloAxisWidth cover)

literalHaloOverlapCount : RegularTranslatedHaloCover → Nat
literalHaloOverlapCount cover =
  fourthPowerCount (haloAxisWidth cover)

literalFourDimensionalHaloOverlap : ∀ cover →
  length (localContainingHaloOffsetEnumeration cover)
  ≡ literalHaloOverlapCount cover
literalFourDimensionalHaloOverlap cover =
  haloOffsetEnumerationLength (haloAxisWidth cover)

------------------------------------------------------------------------
-- Physical origin/offset carrier match.
--
-- A concrete Wilson/RG geometry need only construct the two round trips below.
-- The mapped enumeration then has exactly the already-computed w^4 length, and
-- the round trips provide injectivity and surjectivity rather than relying on a
-- cardinality coincidence.
------------------------------------------------------------------------

record HaloOriginOffsetRoundTrips
    (cover : RegularTranslatedHaloCover)
    (Site : Set) : Set₁ where
  field
    ContainingOrigin : Site → Set
    originFromOffset : ∀ site →
      localContainingHaloOffsets cover → ContainingOrigin site
    offsetFromOrigin : ∀ site →
      ContainingOrigin site → localContainingHaloOffsets cover

    offsetAfterOrigin : ∀ site origin →
      offsetFromOrigin site (originFromOffset site origin) ≡ origin
    originAfterOffset : ∀ site origin →
      originFromOffset site (offsetFromOrigin site origin) ≡ origin

open HaloOriginOffsetRoundTrips public

physicalContainingOriginEnumeration :
  ∀ {cover Site}
    (matching : HaloOriginOffsetRoundTrips cover Site)
    (site : Site) →
  List (ContainingOrigin matching site)
physicalContainingOriginEnumeration {cover} matching site =
  map (originFromOffset matching site)
    (localContainingHaloOffsetEnumeration cover)

physicalContainingOriginEnumerationLength :
  ∀ {cover Site}
    (matching : HaloOriginOffsetRoundTrips cover Site)
    (site : Site) →
  length (physicalContainingOriginEnumeration matching site)
  ≡ literalHaloOverlapCount cover
physicalContainingOriginEnumerationLength {cover} matching site =
  trans
    (lengthMap
      (originFromOffset matching site)
      (localContainingHaloOffsetEnumeration cover))
    (literalFourDimensionalHaloOverlap cover)

offsetToOriginInjective :
  ∀ {cover Site}
    (matching : HaloOriginOffsetRoundTrips cover Site)
    (site : Site) {left right} →
  originFromOffset matching site left ≡ originFromOffset matching site right →
  left ≡ right
offsetToOriginInjective matching site {left} {right} equality =
  trans
    (sym (offsetAfterOrigin matching site left))
    (trans
      (cong (offsetFromOrigin matching site) equality)
      (offsetAfterOrigin matching site right))

everyContainingOriginEnumerated :
  ∀ {cover Site}
    (matching : HaloOriginOffsetRoundTrips cover Site)
    (site : Site) origin →
  originFromOffset matching site (offsetFromOrigin matching site origin)
  ≡ origin
everyContainingOriginEnumerated matching = originAfterOffset matching

fourDimensionalHaloOffsetEnumerationLevel : ProofLevel
fourDimensionalHaloOffsetEnumerationLevel = machineChecked

regularTranslatedHaloOverlapCountLevel : ProofLevel
regularTranslatedHaloOverlapCountLevel = machineChecked

physicalOriginOffsetBijectionAssemblyLevel : ProofLevel
physicalOriginOffsetBijectionAssemblyLevel = machineChecked

physicalBlockOriginOffsetBijectionLevel : ProofLevel
physicalBlockOriginOffsetBijectionLevel = conditional
