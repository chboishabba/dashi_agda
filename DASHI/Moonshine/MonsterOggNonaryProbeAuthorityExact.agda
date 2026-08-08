module DASHI.Moonshine.MonsterOggNonaryProbeAuthorityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem",
-- Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine",
-- Bulletin of the London Mathematical Society 11 (1979), 308--339.
-- DOI: 10.1112/blms/11.3.308.
--
-- DASHI CONTRIBUTION
--
-- Retain p = 9q+r as a coordinate-valued probe on the established Ogg-prime
-- carrier while proving the elementary limitations identified in the roadmap:
--
--   * every prime above 3 automatically lies in a unit residue modulo 9;
--   * complement pairing is the ordinary involution r |-> 9-r;
--   * the proposed three-entry FRACTRAN matching is not one uniform +3 map;
--   * 41 is the fixed point of p |-> 82-p on the displayed depth-two pairs.
--
-- None of these arithmetic facts is promoted to a Monster-module duality,
-- genus-zero theorem, invariant filtration, or explanation of the Ogg list.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

record NonaryProbe (prime : Lane.MonsterPrimeLane) : Set where
  constructor nonary-probe
  field
    coarseSheets : Nat
    fineResidue : Nat
    addressExact :
      Lane.monsterPrimeLaneToNat prime ≡ coarseSheets * 9 + fineResidue

open NonaryProbe public

nonaryProbe : (prime : Lane.MonsterPrimeLane) → NonaryProbe prime
nonaryProbe Lane.p2  = nonary-probe 0 2 refl
nonaryProbe Lane.p3  = nonary-probe 0 3 refl
nonaryProbe Lane.p5  = nonary-probe 0 5 refl
nonaryProbe Lane.p7  = nonary-probe 0 7 refl
nonaryProbe Lane.p11 = nonary-probe 1 2 refl
nonaryProbe Lane.p13 = nonary-probe 1 4 refl
nonaryProbe Lane.p17 = nonary-probe 1 8 refl
nonaryProbe Lane.p19 = nonary-probe 2 1 refl
nonaryProbe Lane.p23 = nonary-probe 2 5 refl
nonaryProbe Lane.p29 = nonary-probe 3 2 refl
nonaryProbe Lane.p31 = nonary-probe 3 4 refl
nonaryProbe Lane.p41 = nonary-probe 4 5 refl
nonaryProbe Lane.p47 = nonary-probe 5 2 refl
nonaryProbe Lane.p59 = nonary-probe 6 5 refl
nonaryProbe Lane.p71 = nonary-probe 7 8 refl

------------------------------------------------------------------------
-- Unit residues modulo 9.  This is an arithmetic consequence of primality
-- above 3, represented here exhaustively for the finite Ogg carrier.
------------------------------------------------------------------------

data UnitResidue9 : Nat → Set where
  unit1 : UnitResidue9 1
  unit2 : UnitResidue9 2
  unit4 : UnitResidue9 4
  unit5 : UnitResidue9 5
  unit7 : UnitResidue9 7
  unit8 : UnitResidue9 8

data OggPrimeAboveThree : Set where
  above5 above7 above11 above13 above17 above19 above23
    above29 above31 above41 above47 above59 above71 : OggPrimeAboveThree

toPrime : OggPrimeAboveThree → Lane.MonsterPrimeLane
toPrime above5 = Lane.p5
toPrime above7 = Lane.p7
toPrime above11 = Lane.p11
toPrime above13 = Lane.p13
toPrime above17 = Lane.p17
toPrime above19 = Lane.p19
toPrime above23 = Lane.p23
toPrime above29 = Lane.p29
toPrime above31 = Lane.p31
toPrime above41 = Lane.p41
toPrime above47 = Lane.p47
toPrime above59 = Lane.p59
toPrime above71 = Lane.p71

allAboveThreeOggResiduesAreUnits :
  (prime : OggPrimeAboveThree) →
  UnitResidue9 (fineResidue (nonaryProbe (toPrime prime)))
allAboveThreeOggResiduesAreUnits above5 = unit5
allAboveThreeOggResiduesAreUnits above7 = unit7
allAboveThreeOggResiduesAreUnits above11 = unit2
allAboveThreeOggResiduesAreUnits above13 = unit4
allAboveThreeOggResiduesAreUnits above17 = unit8
allAboveThreeOggResiduesAreUnits above19 = unit1
allAboveThreeOggResiduesAreUnits above23 = unit5
allAboveThreeOggResiduesAreUnits above29 = unit2
allAboveThreeOggResiduesAreUnits above31 = unit4
allAboveThreeOggResiduesAreUnits above41 = unit5
allAboveThreeOggResiduesAreUnits above47 = unit2
allAboveThreeOggResiduesAreUnits above59 = unit5
allAboveThreeOggResiduesAreUnits above71 = unit8

------------------------------------------------------------------------
-- Complement on the six units is simply additive negation modulo 9.
------------------------------------------------------------------------

complementUnitResidue :
  ∀ {residue} → UnitResidue9 residue → Nat
complementUnitResidue unit1 = 8
complementUnitResidue unit2 = 7
complementUnitResidue unit4 = 5
complementUnitResidue unit5 = 4
complementUnitResidue unit7 = 2
complementUnitResidue unit8 = 1

complementUnitResidueExact :
  ∀ {residue} →
  (unit : UnitResidue9 residue) →
  residue + complementUnitResidue unit ≡ 9
complementUnitResidueExact unit1 = refl
complementUnitResidueExact unit2 = refl
complementUnitResidueExact unit4 = refl
complementUnitResidueExact unit5 = refl
complementUnitResidueExact unit7 = refl
complementUnitResidueExact unit8 = refl

------------------------------------------------------------------------
-- The proposed ordered FRACTRAN matching is not one uniform +3 residue map.
-- The first leg would require 7+3 mod 9 = 2, but its actual translate is 1.
------------------------------------------------------------------------

plusThreeResidue : Nat → Nat
plusThreeResidue 0 = 3
plusThreeResidue 1 = 4
plusThreeResidue 2 = 5
plusThreeResidue 3 = 6
plusThreeResidue 4 = 7
plusThreeResidue 5 = 8
plusThreeResidue 6 = 0
plusThreeResidue 7 = 1
plusThreeResidue 8 = 2
plusThreeResidue other = other

plusThreeTakesTwoToFive : plusThreeResidue 2 ≡ 5
plusThreeTakesTwoToFive = refl

plusThreeTakesFiveToEight : plusThreeResidue 5 ≡ 8
plusThreeTakesFiveToEight = refl

plusThreeDoesNotTakeSevenToTwo : plusThreeResidue 7 ≡ 2 → ⊥
plusThreeDoesNotTakeSevenToTwo ()

record ProposedFractranOrderedPlusThree : Set where
  field
    sevenToTwo : plusThreeResidue 7 ≡ 2
    twoToFive : plusThreeResidue 2 ≡ 5
    fiveToEight : plusThreeResidue 5 ≡ 8

proposedFractranOrderedPlusThreeImpossible :
  ProposedFractranOrderedPlusThree → ⊥
proposedFractranOrderedPlusThreeImpossible proposed =
  plusThreeDoesNotTakeSevenToTwo
    (ProposedFractranOrderedPlusThree.sevenToTwo proposed)

------------------------------------------------------------------------
-- The exact 82-reflection arithmetic around 41.
------------------------------------------------------------------------

data DepthTwoReflectionPair : Set where
  pair11And71 pair23And59 pair41And41 : DepthTwoReflectionPair

leftPrimeValue : DepthTwoReflectionPair → Nat
leftPrimeValue pair11And71 = 11
leftPrimeValue pair23And59 = 23
leftPrimeValue pair41And41 = 41

rightPrimeValue : DepthTwoReflectionPair → Nat
rightPrimeValue pair11And71 = 71
rightPrimeValue pair23And59 = 59
rightPrimeValue pair41And41 = 41

reflectionPairSumsTo82 :
  (pair : DepthTwoReflectionPair) →
  leftPrimeValue pair + rightPrimeValue pair ≡ 82
reflectionPairSumsTo82 pair11And71 = refl
reflectionPairSumsTo82 pair23And59 = refl
reflectionPairSumsTo82 pair41And41 = refl

fortyOneIsReflectionFixedPoint : 41 + 41 ≡ 82
fortyOneIsReflectionFixedPoint = refl

------------------------------------------------------------------------
-- Promotion contracts: arithmetic probes become representation-theoretic only
-- after an actual upstairs operation intertwines with the downstairs probe.
------------------------------------------------------------------------

record NonaryProbeEquivariantPromotion
    (UpstairsObject UpstairsOperation : Set) : Set₁ where
  field
    primeOf : UpstairsObject → Lane.MonsterPrimeLane
    operate : UpstairsOperation → UpstairsObject → UpstairsObject
    residueTransport : UpstairsOperation → Nat → Nat
    probeIntertwines :
      (operation : UpstairsOperation) →
      (object : UpstairsObject) →
      fineResidue (nonaryProbe (primeOf (operate operation object)))
      ≡ residueTransport operation
          (fineResidue (nonaryProbe (primeOf object)))

record MonsterOggNonaryProbeBoundary : Set where
  constructor monster-ogg-nonary-probe-boundary
  field
    allAddressesConstructed : Bool
    allAddressesConstructedIsTrue : allAddressesConstructed ≡ true
    allAboveThreeResiduesUnitCertified : Bool
    allAboveThreeResiduesUnitCertifiedIsTrue :
      allAboveThreeResiduesUnitCertified ≡ true
    proposedUniformPlusThreeRefuted : Bool
    proposedUniformPlusThreeRefutedIsTrue :
      proposedUniformPlusThreeRefuted ≡ true
    actualMonsterEquivariantProbeConstructed : Bool
    actualMonsterEquivariantProbeConstructedIsFalse :
      actualMonsterEquivariantProbeConstructed ≡ false
    genusZeroDerivedFromProbe : Bool
    genusZeroDerivedFromProbeIsFalse : genusZeroDerivedFromProbe ≡ false
    lerayProjectorDerivedFromFortyOne : Bool
    lerayProjectorDerivedFromFortyOneIsFalse :
      lerayProjectorDerivedFromFortyOne ≡ false

canonicalMonsterOggNonaryProbeBoundary : MonsterOggNonaryProbeBoundary
canonicalMonsterOggNonaryProbeBoundary =
  monster-ogg-nonary-probe-boundary
    true refl true refl true refl false refl false refl false refl
