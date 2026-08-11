module DASHI.Biology.IndexedJStratifiedMultiresolutionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Stephane G. Mallat,
-- "A Theory for Multiresolution Signal Decomposition: The Wavelet
-- Representation", IEEE TPAMI 11(7), 1989, 674-693.
-- DOI: 10.1109/34.192463.
--
-- Ingrid Daubechies,
-- "Orthonormal Bases of Compactly Supported Wavelets",
-- Communications on Pure and Applied Mathematics 41(7), 1988, 909-996.
-- DOI: 10.1002/cpa.3160410705.
--
-- DASHI CONTRIBUTION
--
-- Give the indexed-j 1/10/100/... idea an exact finite multiresolution model.
-- The decimal carrier is a homogeneous ten-way address tower.  Its one-step
-- residual is literally the next decimal digit, so the existing
-- MultiscaleMDL split/join becomes exact in both directions for this model.
--
-- Separately, a count profile records the new grade b^r and the cumulative
-- retained count 1 + b + ... + b^r.  Therefore 11, 111, 1111 are cumulative
-- truncation counts in the decimal toy model, while 10, 100, 1000 are the new
-- per-grade counts.  Numeric coincidence with the existing indexed-J "11"
-- is recorded but NOT used to identify the two typed constructions.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.IndexedJExternalGluingExact as Gluing
import DASHI.Biology.IteratedPointedAttachmentSpiralExact as Spiral
import DASHI.Core.MultiscaleMDL as MDL
import DASHI.Foundations.StratifiedResolutionTowerExact as Tower

------------------------------------------------------------------------
-- Homogeneous ten-way address tree.
------------------------------------------------------------------------

data DecimalDigit : Set where
  d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 : DecimalDigit

data DecimalAddress : Nat → Set where
  root : DecimalAddress zero
  extend :
    ∀ {r} →
    DecimalAddress r →
    DecimalDigit →
    DecimalAddress (suc r)

prefix :
  ∀ {r} →
  DecimalAddress (suc r) →
  DecimalAddress r
prefix (extend address digit) = address

lastDigit :
  ∀ {r} →
  DecimalAddress (suc r) →
  DecimalDigit
lastDigit (extend address digit) = digit

decimalResolutionTower : Tower.ResolutionTower
decimalResolutionTower = record
  { Carrier = DecimalAddress
  ; project = prefix
  }

appendZero :
  ∀ {r} →
  DecimalAddress r →
  DecimalAddress (suc r)
appendZero address = extend address d0

prefixAppendZero :
  ∀ {r} (address : DecimalAddress r) →
  prefix (appendZero address) ≡ address
prefixAppendZero address = refl

decimalSplitStructure :
  Tower.SplitResolutionStructure decimalResolutionTower
decimalSplitStructure = record
  { lift = appendZero
  ; project-lift = prefixAppendZero
  }

------------------------------------------------------------------------
-- Existing MDL tower instantiated by the decimal address geometry.
------------------------------------------------------------------------

decimalMultiscaleCarrier : MDL.MultiscaleCarrier
decimalMultiscaleCarrier = record
  { Carrier = DecimalAddress
  ; project = prefix
  ; lift = appendZero
  ; project-lift = prefixAppendZero
  }

decimalResidualCodec : MDL.ResidualCodec decimalMultiscaleCarrier
decimalResidualCodec = record
  { Residual = λ r → DecimalDigit
  ; residual = lastDigit
  ; reconstruct = extend
  ; reconstruct-project-residual = λ where
      (extend address digit) → refl
  }

-- The generic ResidualCodec only requires join(split x) = x.  In this
-- homogeneous decimal model the reverse direction is also exact: every
-- coarse-address/digit pair is admissible.
decimalSplitJoin :
  ∀ {r}
    (pair : MDL.CoarseResidual
      decimalMultiscaleCarrier decimalResidualCodec r) →
  MDL.split decimalResidualCodec (MDL.join decimalResidualCodec pair)
  ≡ pair
decimalSplitJoin (address , digit) = refl

decimalJoinSplit :
  ∀ {r} (fine : DecimalAddress (suc r)) →
  MDL.join decimalResidualCodec (MDL.split decimalResidualCodec fine)
  ≡ fine
decimalJoinSplit = MDL.join-split decimalResidualCodec

------------------------------------------------------------------------
-- A level is simultaneously fine and coarse depending on the cut.
------------------------------------------------------------------------

decimalCut :
  ∀ {r} →
  DecimalAddress (suc r) →
  Tower.CoarseFineCut decimalResolutionTower r
decimalCut = Tower.cutFromFine

decimalMiddleRole :
  ∀ {r} →
  DecimalAddress (suc r) →
  Tower.MiddleLevelRole decimalResolutionTower r
decimalMiddleRole middle =
  Tower.middleLevelRole
    middle
    (prefix middle)
    (extend middle d0)
    refl
    refl

------------------------------------------------------------------------
-- One exact inverse-limit witness: the all-zero decimal history.
------------------------------------------------------------------------

allZeroAddress : (r : Nat) → DecimalAddress r
allZeroAddress zero = root
allZeroAddress (suc r) = extend (allZeroAddress r) d0

allZeroCoherence :
  (r : Nat) →
  prefix (allZeroAddress (suc r)) ≡ allZeroAddress r
allZeroCoherence r = refl

allZeroInverseLimitPoint :
  Tower.InverseLimitPoint decimalResolutionTower
allZeroInverseLimitPoint =
  Tower.inverseLimitPoint allZeroAddress allZeroCoherence

------------------------------------------------------------------------
-- Radix power and cumulative filtered count.
------------------------------------------------------------------------

radixGradeCount : Nat → Nat → Nat
radixGradeCount b zero = 1
radixGradeCount b (suc r) = b * radixGradeCount b r

retainedResolutionCount : Nat → Nat → Nat
retainedResolutionCount b zero = 1
retainedResolutionCount b (suc r) =
  retainedResolutionCount b r + radixGradeCount b (suc r)

retainedResolutionStep :
  (b r : Nat) →
  retainedResolutionCount b (suc r)
  ≡ retainedResolutionCount b r + radixGradeCount b (suc r)
retainedResolutionStep b r = refl

record RadixFilteredCountProfile : Set where
  constructor radixFilteredCountProfile
  field
    radix : Nat
    gradeCount : Nat → Nat
    retainedCount : Nat → Nat
    gradeCountLaw :
      (r : Nat) →
      gradeCount r ≡ radixGradeCount radix r
    retainedBaseLaw :
      retainedCount zero ≡ 1
    retainedStepLaw :
      (r : Nat) →
      retainedCount (suc r)
      ≡ retainedCount r + gradeCount (suc r)

open RadixFilteredCountProfile public

canonicalRadixFilteredCountProfile :
  (b : Nat) → RadixFilteredCountProfile
canonicalRadixFilteredCountProfile b =
  radixFilteredCountProfile
    b
    (radixGradeCount b)
    (retainedResolutionCount b)
    (λ r → refl)
    refl
    (λ r → refl)

------------------------------------------------------------------------
-- Decimal exact values: grades 1,10,100,1000 and cumulative 1,11,111,1111.
------------------------------------------------------------------------

decimalGrade0 : radixGradeCount 10 0 ≡ 1
decimalGrade0 = refl

decimalGrade1 : radixGradeCount 10 1 ≡ 10
decimalGrade1 = refl

decimalGrade2 : radixGradeCount 10 2 ≡ 100
decimalGrade2 = refl

decimalGrade3 : radixGradeCount 10 3 ≡ 1000
decimalGrade3 = refl

decimalRetained0 : retainedResolutionCount 10 0 ≡ 1
decimalRetained0 = refl

decimalRetained1 : retainedResolutionCount 10 1 ≡ 11
decimalRetained1 = refl

decimalRetained2 : retainedResolutionCount 10 2 ≡ 111
decimalRetained2 = refl

decimalRetained3 : retainedResolutionCount 10 3 ≡ 1111
decimalRetained3 = refl

------------------------------------------------------------------------
-- The same construction at arbitrary finite n.
------------------------------------------------------------------------

decimalGradeAt : Nat → Nat
decimalGradeAt = radixGradeCount 10

decimalRetainedThrough : Nat → Nat
decimalRetainedThrough = retainedResolutionCount 10

decimalNextGradeLaw :
  (r : Nat) →
  decimalRetainedThrough (suc r)
  ≡ decimalRetainedThrough r + decimalGradeAt (suc r)
decimalNextGradeLaw = retainedResolutionStep 10

------------------------------------------------------------------------
-- Typed bridge to the existing indexed-J Round-6 construction.
--
-- Both constructions produce the numeral 11 at their first nontrivial stage,
-- but for different reasons:
--   * Round 6: one intrinsic host coordinate + transported external index 10;
--   * Round 7: cumulative count of grade 0 and grade 1, 1 + 10.
-- The equality below is deliberately only an equality in Nat.
------------------------------------------------------------------------

firstCumulativeMatchesJoinedIndexNumerically :
  retainedResolutionCount 10 1 ≡ Gluing.joinedAddressIndex
firstCumulativeMatchesJoinedIndexNumerically =
  trans decimalRetained1 (sym Gluing.joinedAddressIndexIsEleven)

spiralElevenMatchesFirstCumulativeNumerically :
  Spiral.addressIndex Spiral.address11
  ≡ retainedResolutionCount 10 1
spiralElevenMatchesFirstCumulativeNumerically =
  trans refl (sym decimalRetained1)

------------------------------------------------------------------------
-- Pulling coarse data upward is constant on every decimal refinement fibre.
------------------------------------------------------------------------

decimalPullbackConstantOnFibre :
  ∀ {r Value}
    (observable : DecimalAddress r → Value)
    {left right : DecimalAddress (suc r)} →
  prefix left ≡ prefix right →
  Tower.pullbackObservable
    {tower = decimalResolutionTower} observable left
  ≡ Tower.pullbackObservable
      {tower = decimalResolutionTower} observable right
decimalPullbackConstantOnFibre observable proof =
  Tower.pullbackConstantOnFibre
    {tower = decimalResolutionTower}
    observable
    proof

------------------------------------------------------------------------
-- Boundary: keep numeric sequence, state cardinality, and typed J semantics
-- distinct unless an explicit equivalence is constructed.
------------------------------------------------------------------------

record IndexedJMultiresolutionBoundary : Set where
  constructor indexedJMultiresolutionBoundary
  field
    finestLevelTwoHasOneHundredElevenStates : Bool
    finestLevelTwoHasOneHundredElevenStatesIsFalse :
      finestLevelTwoHasOneHundredElevenStates ≡ false

    cumulativeThroughLevelTwoHasCountOneHundredEleven : Bool
    cumulativeThroughLevelTwoHasCountOneHundredElevenIsTrue :
      cumulativeThroughLevelTwoHasCountOneHundredEleven ≡ true

    numericElevenEqualityIdentifiesTypedJConstructions : Bool
    numericElevenEqualityIdentifiesTypedJConstructionsIsFalse :
      numericElevenEqualityIdentifiesTypedJConstructions ≡ false

    decimalTowerIsClaimedAsCanonicalPhysicalRadix : Bool
    decimalTowerIsClaimedAsCanonicalPhysicalRadixIsFalse :
      decimalTowerIsClaimedAsCanonicalPhysicalRadix ≡ false

    allInverseLimitPointsAreEventuallyConstant : Bool
    allInverseLimitPointsAreEventuallyConstantIsFalse :
      allInverseLimitPointsAreEventuallyConstant ≡ false

    decimalAddressInverseLimitIsAutomaticallyTenAdicRing : Bool
    decimalAddressInverseLimitIsAutomaticallyTenAdicRingIsFalse :
      decimalAddressInverseLimitIsAutomaticallyTenAdicRing ≡ false

    finiteGradeCountSuppliesCompletedHilbertDirectSum : Bool
    finiteGradeCountSuppliesCompletedHilbertDirectSumIsFalse :
      finiteGradeCountSuppliesCompletedHilbertDirectSum ≡ false

canonicalIndexedJMultiresolutionBoundary : IndexedJMultiresolutionBoundary
canonicalIndexedJMultiresolutionBoundary =
  indexedJMultiresolutionBoundary
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
