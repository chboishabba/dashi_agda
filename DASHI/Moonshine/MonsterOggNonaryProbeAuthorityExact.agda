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
-- David Ford, John McKay and Simon P. Norton,
-- "More on Replicable Functions",
-- Communications in Algebra 22 (1994), 5175--5193.
-- DOI: 10.1080/00927879408825127.
--
-- John McKay and Heiko Strauss,
-- "The q-series of monstrous moonshine and the decomposition of the head
-- characters",
-- Communications in Algebra 18 (1990), 253--278.
-- DOI: 10.1080/00927879008823911.
--
-- John H. Conway,
-- "FRACTRAN: A Simple Universal Programming Language for Arithmetic",
-- in Open Problems in Communication and Computation, Springer, 1987.
-- No DOI asserted.
--
-- DASHI CONTRIBUTION
--
-- Construct the complete p = 9q+r table for the fifteen Ogg primes and prove:
--
--   * no fine residue is zero or six;
--   * every prime above three has a unit residue modulo nine;
--   * the six units are three complement modes times two orientations;
--   * complement is involutive, preserves mode and reverses orientation;
--   * the sorted FRACTRAN signatures are (7,2,5) and (2,5,8), but are not a
--     single +3 rotation;
--   * the actual FRACTRAN replacements are 23->47, 7->59 and 11->71, and none
--     of those replacement legs is the proposed +3 map;
--   * the exact earning chain reaches 196883 and then 196884 after adjoining
--     one;
--   * 71+10=81, 2*41=81+1, and the three displayed pairs sum to 82;
--   * the repository's semantic carrier partition is exactly 7+7+1, with p71
--     the unique lane in coarse sheet seven;
--   * the unnormalised 7A eta-quotient prefix has constant ten, while the
--     normalized McKay--Thompson Hauptmodul has constant zero.
--
-- None of these finite arithmetic results constructs a transition dynamics,
-- Monster-module splitting, genus-zero proof, Leray projector, explanation of
-- the Ogg list, or Yang--Mills theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_/_)

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import MoonshineEarn as Earn

------------------------------------------------------------------------
-- Complete nonary address table.
------------------------------------------------------------------------

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
-- Exact exclusion of the proposed closed-sheet residues zero and six.
------------------------------------------------------------------------

data OpenNonaryResidue : Nat → Set where
  open1 : OpenNonaryResidue 1
  open2 : OpenNonaryResidue 2
  open3 : OpenNonaryResidue 3
  open4 : OpenNonaryResidue 4
  open5 : OpenNonaryResidue 5
  open7 : OpenNonaryResidue 7
  open8 : OpenNonaryResidue 8

allOggFineResiduesAreOpen :
  (prime : Lane.MonsterPrimeLane) →
  OpenNonaryResidue (fineResidue (nonaryProbe prime))
allOggFineResiduesAreOpen Lane.p2 = open2
allOggFineResiduesAreOpen Lane.p3 = open3
allOggFineResiduesAreOpen Lane.p5 = open5
allOggFineResiduesAreOpen Lane.p7 = open7
allOggFineResiduesAreOpen Lane.p11 = open2
allOggFineResiduesAreOpen Lane.p13 = open4
allOggFineResiduesAreOpen Lane.p17 = open8
allOggFineResiduesAreOpen Lane.p19 = open1
allOggFineResiduesAreOpen Lane.p23 = open5
allOggFineResiduesAreOpen Lane.p29 = open2
allOggFineResiduesAreOpen Lane.p31 = open4
allOggFineResiduesAreOpen Lane.p41 = open5
allOggFineResiduesAreOpen Lane.p47 = open2
allOggFineResiduesAreOpen Lane.p59 = open5
allOggFineResiduesAreOpen Lane.p71 = open8

openResidueAvoidsZero :
  ∀ {residue} → OpenNonaryResidue residue → residue ≡ 0 → ⊥
openResidueAvoidsZero open1 ()
openResidueAvoidsZero open2 ()
openResidueAvoidsZero open3 ()
openResidueAvoidsZero open4 ()
openResidueAvoidsZero open5 ()
openResidueAvoidsZero open7 ()
openResidueAvoidsZero open8 ()

openResidueAvoidsSix :
  ∀ {residue} → OpenNonaryResidue residue → residue ≡ 6 → ⊥
openResidueAvoidsSix open1 ()
openResidueAvoidsSix open2 ()
openResidueAvoidsSix open3 ()
openResidueAvoidsSix open4 ()
openResidueAvoidsSix open5 ()
openResidueAvoidsSix open7 ()
openResidueAvoidsSix open8 ()

allOggFineResiduesAvoidZero :
  (prime : Lane.MonsterPrimeLane) →
  fineResidue (nonaryProbe prime) ≡ 0 → ⊥
allOggFineResiduesAvoidZero prime =
  openResidueAvoidsZero (allOggFineResiduesAreOpen prime)

allOggFineResiduesAvoidSix :
  (prime : Lane.MonsterPrimeLane) →
  fineResidue (nonaryProbe prime) ≡ 6 → ⊥
allOggFineResiduesAvoidSix prime =
  openResidueAvoidsSix (allOggFineResiduesAreOpen prime)

------------------------------------------------------------------------
-- Unit residues and exact complement-mode/orientation quotient.
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

complementUnitResidue : ∀ {residue} → UnitResidue9 residue → Nat
complementUnitResidue unit1 = 8
complementUnitResidue unit2 = 7
complementUnitResidue unit4 = 5
complementUnitResidue unit5 = 4
complementUnitResidue unit7 = 2
complementUnitResidue unit8 = 1

complementUnitWitness :
  ∀ {residue} →
  (unit : UnitResidue9 residue) →
  UnitResidue9 (complementUnitResidue unit)
complementUnitWitness unit1 = unit8
complementUnitWitness unit2 = unit7
complementUnitWitness unit4 = unit5
complementUnitWitness unit5 = unit4
complementUnitWitness unit7 = unit2
complementUnitWitness unit8 = unit1

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

complementUnitResidueInvolutive :
  ∀ {residue} →
  (unit : UnitResidue9 residue) →
  complementUnitResidue (complementUnitWitness unit) ≡ residue
complementUnitResidueInvolutive unit1 = refl
complementUnitResidueInvolutive unit2 = refl
complementUnitResidueInvolutive unit4 = refl
complementUnitResidueInvolutive unit5 = refl
complementUnitResidueInvolutive unit7 = refl
complementUnitResidueInvolutive unit8 = refl

data UnitComplementMode : Set where
  mode18 mode27 mode45 : UnitComplementMode

data UnitOrientation : Set where
  directOrientation counterOrientation : UnitOrientation

unitComplementMode : ∀ {residue} → UnitResidue9 residue → UnitComplementMode
unitComplementMode unit1 = mode18
unitComplementMode unit8 = mode18
unitComplementMode unit2 = mode27
unitComplementMode unit7 = mode27
unitComplementMode unit4 = mode45
unitComplementMode unit5 = mode45

unitOrientation : ∀ {residue} → UnitResidue9 residue → UnitOrientation
unitOrientation unit1 = directOrientation
unitOrientation unit2 = directOrientation
unitOrientation unit4 = directOrientation
unitOrientation unit5 = counterOrientation
unitOrientation unit7 = counterOrientation
unitOrientation unit8 = counterOrientation

flipOrientation : UnitOrientation → UnitOrientation
flipOrientation directOrientation = counterOrientation
flipOrientation counterOrientation = directOrientation

complementPreservesUnitMode :
  ∀ {residue} →
  (unit : UnitResidue9 residue) →
  unitComplementMode (complementUnitWitness unit)
  ≡ unitComplementMode unit
complementPreservesUnitMode unit1 = refl
complementPreservesUnitMode unit2 = refl
complementPreservesUnitMode unit4 = refl
complementPreservesUnitMode unit5 = refl
complementPreservesUnitMode unit7 = refl
complementPreservesUnitMode unit8 = refl

complementFlipsUnitOrientation :
  ∀ {residue} →
  (unit : UnitResidue9 residue) →
  unitOrientation (complementUnitWitness unit)
  ≡ flipOrientation (unitOrientation unit)
complementFlipsUnitOrientation unit1 = refl
complementFlipsUnitOrientation unit2 = refl
complementFlipsUnitOrientation unit4 = refl
complementFlipsUnitOrientation unit5 = refl
complementFlipsUnitOrientation unit7 = refl
complementFlipsUnitOrientation unit8 = refl

------------------------------------------------------------------------
-- Sorted residue signature and correction of the proposed uniform +3 map.
------------------------------------------------------------------------

sortedEarningStartResidues : List Nat
sortedEarningStartResidues = 7 ∷ 2 ∷ 5 ∷ []

sortedEarningEndResidues : List Nat
sortedEarningEndResidues = 2 ∷ 5 ∷ 8 ∷ []

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
-- Actual FRACTRAN replacement relation and exact computation.
------------------------------------------------------------------------

data ActualFractranReplacement : Set where
  replace23By47 replace7By59 replace11By71 : ActualFractranReplacement

replacementSourcePrime : ActualFractranReplacement → Lane.MonsterPrimeLane
replacementSourcePrime replace23By47 = Lane.p23
replacementSourcePrime replace7By59 = Lane.p7
replacementSourcePrime replace11By71 = Lane.p11

replacementTargetPrime : ActualFractranReplacement → Lane.MonsterPrimeLane
replacementTargetPrime replace23By47 = Lane.p47
replacementTargetPrime replace7By59 = Lane.p59
replacementTargetPrime replace11By71 = Lane.p71

replacementSourceResidue : ActualFractranReplacement → Nat
replacementSourceResidue replacement =
  fineResidue (nonaryProbe (replacementSourcePrime replacement))

replacementTargetResidue : ActualFractranReplacement → Nat
replacementTargetResidue replacement =
  fineResidue (nonaryProbe (replacementTargetPrime replacement))

replacement23By47SourceResidueIs5 :
  replacementSourceResidue replace23By47 ≡ 5
replacement23By47SourceResidueIs5 = refl

replacement23By47TargetResidueIs2 :
  replacementTargetResidue replace23By47 ≡ 2
replacement23By47TargetResidueIs2 = refl

replacement7By59SourceResidueIs7 :
  replacementSourceResidue replace7By59 ≡ 7
replacement7By59SourceResidueIs7 = refl

replacement7By59TargetResidueIs5 :
  replacementTargetResidue replace7By59 ≡ 5
replacement7By59TargetResidueIs5 = refl

replacement11By71SourceResidueIs2 :
  replacementSourceResidue replace11By71 ≡ 2
replacement11By71SourceResidueIs2 = refl

replacement11By71TargetResidueIs8 :
  replacementTargetResidue replace11By71 ≡ 8
replacement11By71TargetResidueIs8 = refl

actualFractranReplacementIsNotPlusThree :
  (replacement : ActualFractranReplacement) →
  plusThreeResidue (replacementSourceResidue replacement)
  ≡ replacementTargetResidue replacement → ⊥
actualFractranReplacementIsNotPlusThree replace23By47 ()
actualFractranReplacementIsNotPlusThree replace7By59 ()
actualFractranReplacementIsNotPlusThree replace11By71 ()

actualFractranStepOne : 1771 / 23 * 47 ≡ 3619
actualFractranStepOne = Earn.step1

actualFractranStepTwo : 3619 / 7 * 59 ≡ 30503
actualFractranStepTwo = Earn.step2

actualFractranStepThree : 30503 / 11 * 71 ≡ 196883
actualFractranStepThree = Earn.step3

actualFractranEarningChain :
  (((7 * 11 * 23) / 23 * 47) / 7 * 59) / 11 * 71 ≡ 196883
actualFractranEarningChain = Earn.chain

earnedPrimeProductIs196883 : 47 * 59 * 71 ≡ 196883
earnedPrimeProductIs196883 = Earn.moonshine-product

earnedPrimeProductPlusOneIs196884 : 47 * 59 * 71 + 1 ≡ 196884
earnedPrimeProductPlusOneIs196884 = Earn.observer

------------------------------------------------------------------------
-- Depth-two arithmetic and reflection around 41.
------------------------------------------------------------------------

seventyOnePlusTenCompletesEightyOne : 71 + 10 ≡ 81
seventyOnePlusTenCompletesEightyOne = refl

fortyOneIsPointedMidpointOfEightyOne : 2 * 41 ≡ 81 + 1
fortyOneIsPointedMidpointOfEightyOne = refl

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
-- Precise 7A normalization prefix.
------------------------------------------------------------------------

data SevenAPrefixDegree : Set where
  poleDegree constantDegree qOneDegree qTwoDegree : SevenAPrefixDegree

unnormalizedSevenAEtaQuotientCoefficient : SevenAPrefixDegree → Nat
unnormalizedSevenAEtaQuotientCoefficient poleDegree = 1
unnormalizedSevenAEtaQuotientCoefficient constantDegree = 10
unnormalizedSevenAEtaQuotientCoefficient qOneDegree = 51
unnormalizedSevenAEtaQuotientCoefficient qTwoDegree = 204

normalizedSevenAHauptmodulCoefficient : SevenAPrefixDegree → Nat
normalizedSevenAHauptmodulCoefficient poleDegree = 1
normalizedSevenAHauptmodulCoefficient constantDegree = 0
normalizedSevenAHauptmodulCoefficient qOneDegree = 51
normalizedSevenAHauptmodulCoefficient qTwoDegree = 204

unnormalizedSevenAConstantIsTen :
  unnormalizedSevenAEtaQuotientCoefficient constantDegree ≡ 10
unnormalizedSevenAConstantIsTen = refl

normalizedSevenAConstantIsZero :
  normalizedSevenAHauptmodulCoefficient constantDegree ≡ 0
normalizedSevenAConstantIsZero = refl

sevenANormalizationRemovesTen :
  normalizedSevenAHauptmodulCoefficient constantDegree + 10
  ≡ unnormalizedSevenAEtaQuotientCoefficient constantDegree
sevenANormalizationRemovesTen = refl

sevenAFirstPositiveCoefficientIs51 :
  normalizedSevenAHauptmodulCoefficient qOneDegree ≡ 51
sevenAFirstPositiveCoefficientIs51 = refl

sevenASecondPositiveCoefficientIs204 :
  normalizedSevenAHauptmodulCoefficient qTwoDegree ≡ 204
sevenASecondPositiveCoefficientIs204 = refl

seventyOneDeficitMatchesUnnormalizedSevenAConstant :
  71 + unnormalizedSevenAEtaQuotientCoefficient constantDegree ≡ 81
seventyOneDeficitMatchesUnnormalizedSevenAConstant = refl

------------------------------------------------------------------------
-- Exact semantic 7+7+1 finite carrier partition.
------------------------------------------------------------------------

data MirrorA7Lane : Set where
  mirrorA2 mirrorA3 mirrorA5 mirrorA7 mirrorA11 mirrorA13 mirrorA17 :
    MirrorA7Lane

data MirrorB7Lane : Set where
  mirrorB19 mirrorB23 mirrorB29 mirrorB31 mirrorB41 mirrorB47 mirrorB59 :
    MirrorB7Lane

data Sign1Lane : Set where
  sign71 : Sign1Lane

mirrorA7Prime : MirrorA7Lane → Lane.MonsterPrimeLane
mirrorA7Prime mirrorA2 = Lane.p2
mirrorA7Prime mirrorA3 = Lane.p3
mirrorA7Prime mirrorA5 = Lane.p5
mirrorA7Prime mirrorA7 = Lane.p7
mirrorA7Prime mirrorA11 = Lane.p11
mirrorA7Prime mirrorA13 = Lane.p13
mirrorA7Prime mirrorA17 = Lane.p17

mirrorB7Prime : MirrorB7Lane → Lane.MonsterPrimeLane
mirrorB7Prime mirrorB19 = Lane.p19
mirrorB7Prime mirrorB23 = Lane.p23
mirrorB7Prime mirrorB29 = Lane.p29
mirrorB7Prime mirrorB31 = Lane.p31
mirrorB7Prime mirrorB41 = Lane.p41
mirrorB7Prime mirrorB47 = Lane.p47
mirrorB7Prime mirrorB59 = Lane.p59

sign1Prime : Sign1Lane → Lane.MonsterPrimeLane
sign1Prime sign71 = Lane.p71

canonicalMirrorA7 : List Lane.MonsterPrimeLane
canonicalMirrorA7 =
  Lane.p2 ∷ Lane.p3 ∷ Lane.p5 ∷ Lane.p7 ∷ Lane.p11 ∷ Lane.p13 ∷
  Lane.p17 ∷ []

canonicalMirrorB7 : List Lane.MonsterPrimeLane
canonicalMirrorB7 =
  Lane.p19 ∷ Lane.p23 ∷ Lane.p29 ∷ Lane.p31 ∷ Lane.p41 ∷ Lane.p47 ∷
  Lane.p59 ∷ []

canonicalSign1 : List Lane.MonsterPrimeLane
canonicalSign1 = Lane.p71 ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ rest) = 1 + listCount rest

mirrorA7CountIsSeven : listCount canonicalMirrorA7 ≡ 7
mirrorA7CountIsSeven = refl

mirrorB7CountIsSeven : listCount canonicalMirrorB7 ≡ 7
mirrorB7CountIsSeven = refl

sign1CountIsOne : listCount canonicalSign1 ≡ 1
sign1CountIsOne = refl

semanticSevenSevenOneCountIsFifteen :
  listCount canonicalMirrorA7
  + listCount canonicalMirrorB7
  + listCount canonicalSign1 ≡ 15
semanticSevenSevenOneCountIsFifteen = refl

data BelowSeventhCoarseSheet : Nat → Set where
  belowSheet0 : BelowSeventhCoarseSheet 0
  belowSheet1 : BelowSeventhCoarseSheet 1
  belowSheet2 : BelowSeventhCoarseSheet 2
  belowSheet3 : BelowSeventhCoarseSheet 3
  belowSheet4 : BelowSeventhCoarseSheet 4
  belowSheet5 : BelowSeventhCoarseSheet 5
  belowSheet6 : BelowSeventhCoarseSheet 6

mirrorA7BelowSeventhCoarseSheet :
  (lane : MirrorA7Lane) →
  BelowSeventhCoarseSheet
    (coarseSheets (nonaryProbe (mirrorA7Prime lane)))
mirrorA7BelowSeventhCoarseSheet mirrorA2 = belowSheet0
mirrorA7BelowSeventhCoarseSheet mirrorA3 = belowSheet0
mirrorA7BelowSeventhCoarseSheet mirrorA5 = belowSheet0
mirrorA7BelowSeventhCoarseSheet mirrorA7 = belowSheet0
mirrorA7BelowSeventhCoarseSheet mirrorA11 = belowSheet1
mirrorA7BelowSeventhCoarseSheet mirrorA13 = belowSheet1
mirrorA7BelowSeventhCoarseSheet mirrorA17 = belowSheet1

mirrorB7BelowSeventhCoarseSheet :
  (lane : MirrorB7Lane) →
  BelowSeventhCoarseSheet
    (coarseSheets (nonaryProbe (mirrorB7Prime lane)))
mirrorB7BelowSeventhCoarseSheet mirrorB19 = belowSheet2
mirrorB7BelowSeventhCoarseSheet mirrorB23 = belowSheet2
mirrorB7BelowSeventhCoarseSheet mirrorB29 = belowSheet3
mirrorB7BelowSeventhCoarseSheet mirrorB31 = belowSheet3
mirrorB7BelowSeventhCoarseSheet mirrorB41 = belowSheet4
mirrorB7BelowSeventhCoarseSheet mirrorB47 = belowSheet5
mirrorB7BelowSeventhCoarseSheet mirrorB59 = belowSheet6

sign1CoarseSheetIsSeven :
  coarseSheets (nonaryProbe (sign1Prime sign71)) ≡ 7
sign1CoarseSheetIsSeven = refl

sign1FineResidueIsEight :
  fineResidue (nonaryProbe (sign1Prime sign71)) ≡ 8
sign1FineResidueIsEight = refl

------------------------------------------------------------------------
-- Promotion contract and exact boundary.
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
    closedResiduesZeroAndSixExcluded : Bool
    closedResiduesZeroAndSixExcludedIsTrue :
      closedResiduesZeroAndSixExcluded ≡ true
    complementModeOrientationConstructed : Bool
    complementModeOrientationConstructedIsTrue :
      complementModeOrientationConstructed ≡ true
    proposedUniformPlusThreeRefuted : Bool
    proposedUniformPlusThreeRefutedIsTrue :
      proposedUniformPlusThreeRefuted ≡ true
    actualFractranReplacementIsUniformPlusThree : Bool
    actualFractranReplacementIsUniformPlusThreeIsFalse :
      actualFractranReplacementIsUniformPlusThree ≡ false
    sevenSevenOneFinitePartitionConstructed : Bool
    sevenSevenOneFinitePartitionConstructedIsTrue :
      sevenSevenOneFinitePartitionConstructed ≡ true
    normalizedSevenAConstantTermIsTen : Bool
    normalizedSevenAConstantTermIsTenIsFalse :
      normalizedSevenAConstantTermIsTen ≡ false
    rawSevenAConstantIsMonsterSurvivingMass : Bool
    rawSevenAConstantIsMonsterSurvivingMassIsFalse :
      rawSevenAConstantIsMonsterSurvivingMass ≡ false
    actualForwardTransitionConstructed : Bool
    actualForwardTransitionConstructedIsFalse :
      actualForwardTransitionConstructed ≡ false
    actualMonsterEquivariantProbeConstructed : Bool
    actualMonsterEquivariantProbeConstructedIsFalse :
      actualMonsterEquivariantProbeConstructed ≡ false
    genusZeroDerivedFromProbe : Bool
    genusZeroDerivedFromProbeIsFalse : genusZeroDerivedFromProbe ≡ false
    genusZeroEquivalentToAcyclicCascade : Bool
    genusZeroEquivalentToAcyclicCascadeIsFalse :
      genusZeroEquivalentToAcyclicCascade ≡ false
    lerayProjectorDerivedFromFortyOne : Bool
    lerayProjectorDerivedFromFortyOneIsFalse :
      lerayProjectorDerivedFromFortyOne ≡ false
    sevenSevenOneIsMonsterModuleDecomposition : Bool
    sevenSevenOneIsMonsterModuleDecompositionIsFalse :
      sevenSevenOneIsMonsterModuleDecomposition ≡ false
    clayYangMillsPromoted : Bool
    clayYangMillsPromotedIsFalse : clayYangMillsPromoted ≡ false

canonicalMonsterOggNonaryProbeBoundary : MonsterOggNonaryProbeBoundary
canonicalMonsterOggNonaryProbeBoundary =
  monster-ogg-nonary-probe-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
