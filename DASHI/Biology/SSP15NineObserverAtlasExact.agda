module DASHI.Biology.SSP15NineObserverAtlasExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / COMPUTATIONAL REFERENCES
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem",
-- Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- Thomas Breuer,
-- "The GAP Character Table Library", Version 1.3.11 (2025).
-- No DOI assigned.
--
-- Alexander Hulpke,
-- GAP Transitive Groups Library, degree-nine data.
-- No DOI assigned.
--
-- John H. Conway, Robert T. Curtis, Simon P. Norton, Richard A. Parker,
-- and Robert A. Wilson,
-- "Atlas of Finite Groups", Oxford University Press, 1985.
-- ISBN: 978-0-19-853199-9; no DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Type the provisional nine-observer atlas lane by lane, separating exact
-- arithmetic identities from externally sourced character-table counts and
-- from interpretations that still require a concrete action/projector model.
-- The pointed-sign construction itself is an actual carrier constructor, and
-- all six edges among the Ogg values are proved by exact arithmetic.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Quotient
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- Observer classification.  The constructor names state what is being counted
-- and prevent one observer kind from silently replacing another.
------------------------------------------------------------------------

data NineObserverKind : Set where
  reflectionIrrepCount : NineObserverKind
  ternaryAxisIrrepCount : NineObserverKind
  squareIrrepCount : NineObserverKind
  affineSpecialLinearIrrepCount : NineObserverKind
  qutritHeisenbergIrrepCount : NineObserverKind
  projectiveCompletionCount : NineObserverKind
  cyclicWreathIrrepCount : NineObserverKind
  pointedEvenPermutationSpectrum : NineObserverKind
  pointedBlockWreathSpectrum : NineObserverKind
  reducedFullPermutationSpectrum : NineObserverKind
  pointedFullPermutationSpectrum : NineObserverKind
  depthTwoInversionOrbitCount : NineObserverKind
  depthTwoThirtyFourComplement : NineObserverKind
  depthTwoTwentyTwoComplement : NineObserverKind
  depthTwoTenComplement : NineObserverKind

data AtlasAuthority : Set where
  exactFiniteArithmetic : AtlasAuthority
  externalCharacterTableValue : AtlasAuthority
  externalFiniteGeometryValue : AtlasAuthority
  candidateObserverInterpretation : AtlasAuthority

record SSP15NineAtlasEntry (prime : Lane.MonsterPrimeLane) : Set where
  constructor ssp15-nine-atlas-entry
  field
    observerKind : NineObserverKind
    observedValue : Nat
    observedValueIsPrimeLane :
      observedValue ≡ Lane.monsterPrimeLaneToNat prime
    nonaryDepth : Nat
    authority : AtlasAuthority
    concreteActionConstructedHere : Bool

open SSP15NineAtlasEntry public

ssp15NineAtlas :
  (prime : Lane.MonsterPrimeLane) → SSP15NineAtlasEntry prime
ssp15NineAtlas Lane.p2 =
  ssp15-nine-atlas-entry
    reflectionIrrepCount 2 refl 1 externalCharacterTableValue false
ssp15NineAtlas Lane.p3 =
  ssp15-nine-atlas-entry
    ternaryAxisIrrepCount 3 refl 1 externalCharacterTableValue false
ssp15NineAtlas Lane.p5 =
  ssp15-nine-atlas-entry
    squareIrrepCount 5 refl 1 externalCharacterTableValue false
ssp15NineAtlas Lane.p7 =
  ssp15-nine-atlas-entry
    affineSpecialLinearIrrepCount 7 refl 1 externalCharacterTableValue false
ssp15NineAtlas Lane.p11 =
  ssp15-nine-atlas-entry
    qutritHeisenbergIrrepCount 11 refl 1 candidateObserverInterpretation false
ssp15NineAtlas Lane.p13 =
  ssp15-nine-atlas-entry
    projectiveCompletionCount 13 refl 1 externalFiniteGeometryValue false
ssp15NineAtlas Lane.p17 =
  ssp15-nine-atlas-entry
    cyclicWreathIrrepCount 17 refl 1 externalCharacterTableValue false
ssp15NineAtlas Lane.p19 =
  ssp15-nine-atlas-entry
    pointedEvenPermutationSpectrum 19 refl 1 externalCharacterTableValue false
ssp15NineAtlas Lane.p23 =
  ssp15-nine-atlas-entry
    pointedBlockWreathSpectrum 23 refl 1 externalCharacterTableValue false
ssp15NineAtlas Lane.p29 =
  ssp15-nine-atlas-entry
    reducedFullPermutationSpectrum 29 refl 1 externalCharacterTableValue false
ssp15NineAtlas Lane.p31 =
  ssp15-nine-atlas-entry
    pointedFullPermutationSpectrum 31 refl 1 externalCharacterTableValue false
ssp15NineAtlas Lane.p41 =
  ssp15-nine-atlas-entry
    depthTwoInversionOrbitCount 41 refl 2 exactFiniteArithmetic false
ssp15NineAtlas Lane.p47 =
  ssp15-nine-atlas-entry
    depthTwoThirtyFourComplement 47 refl 2 candidateObserverInterpretation false
ssp15NineAtlas Lane.p59 =
  ssp15-nine-atlas-entry
    depthTwoTwentyTwoComplement 59 refl 2 candidateObserverInterpretation false
ssp15NineAtlas Lane.p71 =
  ssp15-nine-atlas-entry
    depthTwoTenComplement 71 refl 2 exactFiniteArithmetic false

------------------------------------------------------------------------
-- Exact arithmetic behind the observer labels.
------------------------------------------------------------------------

qutritHeisenbergCountArithmetic : 9 + 2 ≡ 11
qutritHeisenbergCountArithmetic = refl

projectiveCompletionArithmetic : 9 + 4 ≡ 13
projectiveCompletionArithmetic = refl

pointedEvenPermutationArithmetic : 1 + 18 ≡ 19
pointedEvenPermutationArithmetic = refl

pointedBlockWreathArithmetic : 1 + 22 ≡ 23
pointedBlockWreathArithmetic = refl

reducedFullPermutationArithmetic : 29 + 1 ≡ 30
reducedFullPermutationArithmetic = refl

pointedFullPermutationArithmetic : 1 + 30 ≡ 31
pointedFullPermutationArithmetic = refl

depthTwoInversionOrbitArithmetic : 2 * 41 ≡ 81 + 1
depthTwoInversionOrbitArithmetic = refl

depthTwoThirtyFourComplementArithmetic : 47 + 34 ≡ 81
depthTwoThirtyFourComplementArithmetic = refl

depthTwoTwentyTwoComplementArithmetic : 59 + 22 ≡ 81
depthTwoTwentyTwoComplementArithmetic = refl

depthTwoTenComplementArithmetic : 71 + 10 ≡ 81
depthTwoTenComplementArithmetic = refl

------------------------------------------------------------------------
-- Actual pointed-sign carrier constructor.
------------------------------------------------------------------------

data PointedSignedCarrier (X : Set) : Set where
  distinguishedObserver : PointedSignedCarrier X
  signedPoint : X → Quotient.BinaryPhase → PointedSignedCarrier X

mapPointedSigned :
  ∀ {X Y : Set} → (X → Y) → PointedSignedCarrier X → PointedSignedCarrier Y
mapPointedSigned map distinguishedObserver = distinguishedObserver
mapPointedSigned map (signedPoint point phase) = signedPoint (map point) phase

mapPointedSignedIdentity :
  ∀ {X : Set} →
  (point : PointedSignedCarrier X) →
  mapPointedSigned (λ value → value) point ≡ point
mapPointedSignedIdentity distinguishedObserver = refl
mapPointedSignedIdentity (signedPoint point phase) = refl

pointedSignedCardinalityValue : Nat → Nat
pointedSignedCardinalityValue cardinality = 2 * cardinality + 1

pointedSignedTwoIsFive : pointedSignedCardinalityValue 2 ≡ 5
pointedSignedTwoIsFive = refl

pointedSignedFiveIsEleven : pointedSignedCardinalityValue 5 ≡ 11
pointedSignedFiveIsEleven = refl

pointedSignedElevenIsTwentyThree : pointedSignedCardinalityValue 11 ≡ 23
pointedSignedElevenIsTwentyThree = refl

pointedSignedTwentyThreeIsFortySeven :
  pointedSignedCardinalityValue 23 ≡ 47
pointedSignedTwentyThreeIsFortySeven = refl

pointedSignedThreeIsSeven : pointedSignedCardinalityValue 3 ≡ 7
pointedSignedThreeIsSeven = refl

pointedSignedTwentyNineIsFiftyNine :
  pointedSignedCardinalityValue 29 ≡ 59
pointedSignedTwentyNineIsFiftyNine = refl

------------------------------------------------------------------------
-- Contract required to promote an arithmetic atlas entry to a genuine
-- projector-and-transport realization.
------------------------------------------------------------------------

record SSP15NineRealisation (prime : Lane.MonsterPrimeLane) : Set₁ where
  field
    NineCarrier : Set
    Symmetry : Set
    action : Symmetry → NineCarrier → NineCarrier
    observerKind : NineObserverKind
    observedValue : Nat
    valueIsPrime : observedValue ≡ Lane.monsterPrimeLaneToNat prime
    Projector : Set
    projectorActs : Projector → NineCarrier → NineCarrier
    transportEquivariant : Set
    decompositionCertified : Set

record SSP15NineObserverAtlasBoundary : Set where
  constructor ssp15-nine-observer-atlas-boundary
  field
    allFifteenEntriesTyped : Bool
    allFifteenEntriesTypedIsTrue : allFifteenEntriesTyped ≡ true
    pointedSignedCarrierConstructed : Bool
    pointedSignedCarrierConstructedIsTrue :
      pointedSignedCarrierConstructed ≡ true
    externalCharacterCountsReprovedInternally : Bool
    externalCharacterCountsReprovedInternallyIsFalse :
      externalCharacterCountsReprovedInternally ≡ false
    allFifteenActionsAndProjectorsConstructed : Bool
    allFifteenActionsAndProjectorsConstructedIsFalse :
      allFifteenActionsAndProjectorsConstructed ≡ false

canonicalSSP15NineObserverAtlasBoundary : SSP15NineObserverAtlasBoundary
canonicalSSP15NineObserverAtlasBoundary =
  ssp15-nine-observer-atlas-boundary true refl true refl false refl false refl
