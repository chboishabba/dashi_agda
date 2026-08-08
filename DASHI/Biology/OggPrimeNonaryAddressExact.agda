module DASHI.Biology.OggPrimeNonaryAddressExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem",
-- Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- DASHI CONTRIBUTION
--
-- Give every one of the fifteen established Monster/Ogg prime lanes an exact
-- Euclidean address p = 9 q + r.  The residue is represented by an ordinary
-- digit of the completed nonary carrier, hence it has a complement mode and a
-- binary orientation.  All lanes except p=3 occupy the three phase-mobile
-- unit-mode pairs {1,8}, {2,7}, and {4,5}; p=3 is the exceptional triadic
-- closure lane.  Pointed-sign lift edges and the depth-two 81-complement ledger
-- are represented by exact arithmetic proofs.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Quotient
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- Ordinary digit values.  j9 is the carried completion state and is not used
-- as a remainder in the Euclidean addresses 0 <= r < 9.
------------------------------------------------------------------------

stateValue : Quotient.DecimalCompletionState → Nat
stateValue Quotient.d0 = 0
stateValue Quotient.d1 = 1
stateValue Quotient.d2 = 2
stateValue Quotient.d3 = 3
stateValue Quotient.d4 = 4
stateValue Quotient.d5 = 5
stateValue Quotient.d6 = 6
stateValue Quotient.d7 = 7
stateValue Quotient.d8 = 8
stateValue Quotient.j9 = 9

record NonaryOggAddress (prime : Lane.MonsterPrimeLane) : Set where
  constructor nonary-ogg-address
  field
    coarseSheets : Nat
    fineState : Quotient.DecimalCompletionState
    remainder : Nat
    remainderIsFineStateValue : stateValue fineState ≡ remainder
    addressExact :
      Lane.monsterPrimeLaneToNat prime ≡ coarseSheets * 9 + remainder
    complementMode : Quotient.ComplementMode5
    complementModeExact :
      Quotient.complementMode fineState ≡ complementMode
    binaryOrientation : Quotient.BinaryPhase
    binaryOrientationExact :
      Quotient.binaryPhase fineState ≡ binaryOrientation

open NonaryOggAddress public

nonaryOggAddress :
  (prime : Lane.MonsterPrimeLane) → NonaryOggAddress prime
nonaryOggAddress Lane.p2 =
  nonary-ogg-address 0 Quotient.d2 2 refl refl
    Quotient.mode27 refl Quotient.directPhase refl
nonaryOggAddress Lane.p3 =
  nonary-ogg-address 0 Quotient.d3 3 refl refl
    Quotient.mode36 refl Quotient.directPhase refl
nonaryOggAddress Lane.p5 =
  nonary-ogg-address 0 Quotient.d5 5 refl refl
    Quotient.mode45 refl Quotient.counterPhase refl
nonaryOggAddress Lane.p7 =
  nonary-ogg-address 0 Quotient.d7 7 refl refl
    Quotient.mode27 refl Quotient.counterPhase refl
nonaryOggAddress Lane.p11 =
  nonary-ogg-address 1 Quotient.d2 2 refl refl
    Quotient.mode27 refl Quotient.directPhase refl
nonaryOggAddress Lane.p13 =
  nonary-ogg-address 1 Quotient.d4 4 refl refl
    Quotient.mode45 refl Quotient.directPhase refl
nonaryOggAddress Lane.p17 =
  nonary-ogg-address 1 Quotient.d8 8 refl refl
    Quotient.mode18 refl Quotient.counterPhase refl
nonaryOggAddress Lane.p19 =
  nonary-ogg-address 2 Quotient.d1 1 refl refl
    Quotient.mode18 refl Quotient.directPhase refl
nonaryOggAddress Lane.p23 =
  nonary-ogg-address 2 Quotient.d5 5 refl refl
    Quotient.mode45 refl Quotient.counterPhase refl
nonaryOggAddress Lane.p29 =
  nonary-ogg-address 3 Quotient.d2 2 refl refl
    Quotient.mode27 refl Quotient.directPhase refl
nonaryOggAddress Lane.p31 =
  nonary-ogg-address 3 Quotient.d4 4 refl refl
    Quotient.mode45 refl Quotient.directPhase refl
nonaryOggAddress Lane.p41 =
  nonary-ogg-address 4 Quotient.d5 5 refl refl
    Quotient.mode45 refl Quotient.counterPhase refl
nonaryOggAddress Lane.p47 =
  nonary-ogg-address 5 Quotient.d2 2 refl refl
    Quotient.mode27 refl Quotient.directPhase refl
nonaryOggAddress Lane.p59 =
  nonary-ogg-address 6 Quotient.d5 5 refl refl
    Quotient.mode45 refl Quotient.counterPhase refl
nonaryOggAddress Lane.p71 =
  nonary-ogg-address 7 Quotient.d8 8 refl refl
    Quotient.mode18 refl Quotient.counterPhase refl

------------------------------------------------------------------------
-- The nonexceptional prime lanes occupy exactly the three unit complement
-- modes.  This is finite exhaustive arithmetic, not a generic primality proof.
------------------------------------------------------------------------

data PhaseMobileMode : Quotient.ComplementMode5 → Set where
  mobile18 : PhaseMobileMode Quotient.mode18
  mobile27 : PhaseMobileMode Quotient.mode27
  mobile45 : PhaseMobileMode Quotient.mode45

data NonThreeOggLane : Set where
  lane2 lane5 lane7 lane11 lane13 lane17 lane19
    lane23 lane29 lane31 lane41 lane47 lane59 lane71 : NonThreeOggLane

toOggLane : NonThreeOggLane → Lane.MonsterPrimeLane
toOggLane lane2 = Lane.p2
toOggLane lane5 = Lane.p5
toOggLane lane7 = Lane.p7
toOggLane lane11 = Lane.p11
toOggLane lane13 = Lane.p13
toOggLane lane17 = Lane.p17
toOggLane lane19 = Lane.p19
toOggLane lane23 = Lane.p23
toOggLane lane29 = Lane.p29
toOggLane lane31 = Lane.p31
toOggLane lane41 = Lane.p41
toOggLane lane47 = Lane.p47
toOggLane lane59 = Lane.p59
toOggLane lane71 = Lane.p71

nonThreeLaneModeIsPhaseMobile :
  (prime : NonThreeOggLane) →
  PhaseMobileMode
    (complementMode (nonaryOggAddress (toOggLane prime)))
nonThreeLaneModeIsPhaseMobile lane2 = mobile27
nonThreeLaneModeIsPhaseMobile lane5 = mobile45
nonThreeLaneModeIsPhaseMobile lane7 = mobile27
nonThreeLaneModeIsPhaseMobile lane11 = mobile27
nonThreeLaneModeIsPhaseMobile lane13 = mobile45
nonThreeLaneModeIsPhaseMobile lane17 = mobile18
nonThreeLaneModeIsPhaseMobile lane19 = mobile18
nonThreeLaneModeIsPhaseMobile lane23 = mobile45
nonThreeLaneModeIsPhaseMobile lane29 = mobile27
nonThreeLaneModeIsPhaseMobile lane31 = mobile45
nonThreeLaneModeIsPhaseMobile lane41 = mobile45
nonThreeLaneModeIsPhaseMobile lane47 = mobile27
nonThreeLaneModeIsPhaseMobile lane59 = mobile45
nonThreeLaneModeIsPhaseMobile lane71 = mobile18

threeLaneIsTriadicClosureMode :
  complementMode (nonaryOggAddress Lane.p3) ≡ Quotient.mode36
threeLaneIsTriadicClosureMode = refl

threeLaneIsDirectOrientation :
  binaryOrientation (nonaryOggAddress Lane.p3) ≡ Quotient.directPhase
threeLaneIsDirectOrientation = refl

------------------------------------------------------------------------
-- Pointed-sign lifts internal to the fifteen Ogg values.
------------------------------------------------------------------------

data PointedSignedEdge :
    Lane.MonsterPrimeLane → Lane.MonsterPrimeLane → Set where
  edge2to5 : PointedSignedEdge Lane.p2 Lane.p5
  edge5to11 : PointedSignedEdge Lane.p5 Lane.p11
  edge11to23 : PointedSignedEdge Lane.p11 Lane.p23
  edge23to47 : PointedSignedEdge Lane.p23 Lane.p47
  edge3to7 : PointedSignedEdge Lane.p3 Lane.p7
  edge29to59 : PointedSignedEdge Lane.p29 Lane.p59

pointedSignedEdgeExact :
  ∀ {source target} →
  PointedSignedEdge source target →
  Lane.monsterPrimeLaneToNat target
  ≡ 2 * Lane.monsterPrimeLaneToNat source + 1
pointedSignedEdgeExact edge2to5 = refl
pointedSignedEdgeExact edge5to11 = refl
pointedSignedEdgeExact edge11to23 = refl
pointedSignedEdgeExact edge23to47 = refl
pointedSignedEdgeExact edge3to7 = refl
pointedSignedEdgeExact edge29to59 = refl

------------------------------------------------------------------------
-- Depth-two nonary arithmetic.
------------------------------------------------------------------------

fiveIsHalfOfPointedNineDivisionFree : 2 * 5 ≡ 9 + 1
fiveIsHalfOfPointedNineDivisionFree = refl

fortyOneIsHalfOfPointedEightyOneDivisionFree : 2 * 41 ≡ 81 + 1
fortyOneIsHalfOfPointedEightyOneDivisionFree = refl

seventyOneRemovesCompleteBinaryFiveInterface : 71 + 5 * 2 ≡ 81
seventyOneRemovesCompleteBinaryFiveInterface = refl

record DepthTwoNonaryComplementLedger : Set where
  constructor depth-two-nonary-complement-ledger
  field
    fortyOnePlusForty : 41 + 40 ≡ 81
    fortySevenPlusThirtyFour : 47 + 34 ≡ 81
    fiftyNinePlusTwentyTwo : 59 + 22 ≡ 81
    seventyOnePlusTen : 71 + 10 ≡ 81
    fortySevenAlsoPointedLiftOfTwentyThree : 47 ≡ 2 * 23 + 1
    fiftyNineAlsoPointedLiftOfTwentyNine : 59 ≡ 2 * 29 + 1

canonicalDepthTwoNonaryComplementLedger : DepthTwoNonaryComplementLedger
canonicalDepthTwoNonaryComplementLedger =
  depth-two-nonary-complement-ledger refl refl refl refl refl refl

canonicalOggAddresses :
  List (Lane.MonsterPrimeLane)
canonicalOggAddresses = Lane.canonicalMonsterPrimeLane

record OggPrimeNonaryAddressBoundary : Set where
  constructor ogg-prime-nonary-address-boundary
  field
    allFifteenAddressesConstructed : Bool
    allFifteenAddressesConstructedIsTrue :
      allFifteenAddressesConstructed ≡ true
    arithmeticAddressIsSupersingularJProof : Bool
    arithmeticAddressIsSupersingularJProofIsFalse :
      arithmeticAddressIsSupersingularJProof ≡ false
    depthTwoComplementArithmeticConstructsInvariantSubmodule : Bool
    depthTwoComplementArithmeticConstructsInvariantSubmoduleIsFalse :
      depthTwoComplementArithmeticConstructsInvariantSubmodule ≡ false

canonicalOggPrimeNonaryAddressBoundary : OggPrimeNonaryAddressBoundary
canonicalOggPrimeNonaryAddressBoundary =
  ogg-prime-nonary-address-boundary true refl false refl false refl
