module DASHI.Moonshine.Monster3BCyclicFourierDyadicBridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine",
-- Bulletin of the London Mathematical Society 11 (1979), 308--339.
-- DOI: 10.1112/blms/11.3.308.
--
-- R. W. Barraclough and R. A. Wilson,
-- "The Character Table of a Maximal Subgroup of the Monster",
-- LMS Journal of Computation and Mathematics 10 (2007), 161--175.
-- DOI: 10.1112/S1461157000001352.
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks",
-- Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- DASHI CONTRIBUTION
--
-- Put the 3B eigenspace split, the all-1/all-2/all-3 functionals, the
-- ordered 1-2-3 and 3-6-9 functionals, and the apparently unrelated
-- denominator 196608 into one exact arithmetic chart.
--
-- The key nontrivial refinement is
--
--   (65663,65610,65610)
--     = 65536 (1,1,1) + (127,74,74).
--
-- Hence
--
--   196883 = 196608 + 275,
--   53     = 127 - 74,
--
-- and for V^natural_2 = 1 + W,
--
--   196884 = 196608 + 276,
--   54     = 128 - 74.
--
-- This is a genuine common decomposition of the integers.  It does not by
-- itself assert that the Yang--Mills denominator was representation-
-- theoretically selected by the Monster.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

record ThreePhaseMultiplicity : Set where
  constructor threePhaseMultiplicity
  field
    invariant : Nat
    zeta : Nat
    zetaSquared : Nat

open ThreePhaseMultiplicity public

phaseDimension : ThreePhaseMultiplicity → Nat
phaseDimension m = invariant m + zeta m + zetaSquared m

uniformOne : ThreePhaseMultiplicity → Nat
uniformOne = phaseDimension

uniformTwo : ThreePhaseMultiplicity → Nat
uniformTwo m = 2 * invariant m + 2 * zeta m + 2 * zetaSquared m

uniformThree : ThreePhaseMultiplicity → Nat
uniformThree m = 3 * invariant m + 3 * zeta m + 3 * zetaSquared m

orderedOneTwoThree : ThreePhaseMultiplicity → Nat
orderedOneTwoThree m = invariant m + 2 * zeta m + 3 * zetaSquared m

orderedThreeTwoOne : ThreePhaseMultiplicity → Nat
orderedThreeTwoOne m = 3 * invariant m + 2 * zeta m + zetaSquared m

orderedThreeSixNine : ThreePhaseMultiplicity → Nat
orderedThreeSixNine m = 3 * invariant m + 6 * zeta m + 9 * zetaSquared m

monsterW3B : ThreePhaseMultiplicity
monsterW3B = threePhaseMultiplicity 65663 65610 65610

moonshineWeightTwo3B : ThreePhaseMultiplicity
moonshineWeightTwo3B = threePhaseMultiplicity 65664 65610 65610

monsterWDimension : phaseDimension monsterW3B ≡ 196883
monsterWDimension = refl

moonshineWeightTwoDimension : phaseDimension moonshineWeightTwo3B ≡ 196884
moonshineWeightTwoDimension = refl

------------------------------------------------------------------------
-- The C3 Fourier residual, represented without importing complex numbers.
-- Equal nontrivial multiplicities imply
--
--   m0 + zeta m + zeta^2 m = m0 - m.
--
-- We record subtraction as an additive certificate.
------------------------------------------------------------------------

monsterWCharacterResidual : zeta monsterW3B + 53 ≡ invariant monsterW3B
monsterWCharacterResidual = refl

moonshineWeightTwoCharacterResidual :
  zeta moonshineWeightTwo3B + 54 ≡ invariant moonshineWeightTwo3B
moonshineWeightTwoCharacterResidual = refl

balancedRegularBulkDimension : Nat
balancedRegularBulkDimension = 3 * 65610

balancedRegularBulkDimensionIs196830 :
  balancedRegularBulkDimension ≡ 196830
balancedRegularBulkDimensionIs196830 = refl

balancedBulkPlusResidualIsMonsterW :
  balancedRegularBulkDimension + 53 ≡ 196883
balancedBulkPlusResidualIsMonsterW = refl

------------------------------------------------------------------------
-- The exact dyadic baseline.
------------------------------------------------------------------------

dyadicPhaseBaseline : Nat
dyadicPhaseBaseline = 65536

dyadicSymmetricBulk : Nat
dyadicSymmetricBulk = 3 * dyadicPhaseBaseline

dyadicSymmetricBulkIs196608 : dyadicSymmetricBulk ≡ 196608
dyadicSymmetricBulkIs196608 = refl

invariantDyadicCorrection : Nat
invariantDyadicCorrection = 127

nontrivialDyadicCorrection : Nat
nontrivialDyadicCorrection = 74

invariantPhaseSplitsAtTwoPowerSixteen :
  dyadicPhaseBaseline + invariantDyadicCorrection ≡ invariant monsterW3B
invariantPhaseSplitsAtTwoPowerSixteen = refl

zetaPhaseSplitsAtTwoPowerSixteen :
  dyadicPhaseBaseline + nontrivialDyadicCorrection ≡ zeta monsterW3B
zetaPhaseSplitsAtTwoPowerSixteen = refl

zetaSquaredPhaseSplitsAtTwoPowerSixteen :
  dyadicPhaseBaseline + nontrivialDyadicCorrection ≡ zetaSquared monsterW3B
zetaSquaredPhaseSplitsAtTwoPowerSixteen = refl

dyadicResidualDimension : Nat
dyadicResidualDimension =
  invariantDyadicCorrection
  + nontrivialDyadicCorrection
  + nontrivialDyadicCorrection

dyadicResidualDimensionIs275 : dyadicResidualDimension ≡ 275
dyadicResidualDimensionIs275 = refl

dyadicBulkPlusResidualIsMonsterW :
  dyadicSymmetricBulk + dyadicResidualDimension ≡ 196883
dyadicBulkPlusResidualIsMonsterW = refl

dyadicResidualCharacterIs53 :
  nontrivialDyadicCorrection + 53 ≡ invariantDyadicCorrection
dyadicResidualCharacterIs53 = refl

weightTwoInvariantCorrection : Nat
weightTwoInvariantCorrection = 128

weightTwoResidualDimension : Nat
weightTwoResidualDimension =
  weightTwoInvariantCorrection
  + nontrivialDyadicCorrection
  + nontrivialDyadicCorrection

weightTwoResidualDimensionIs276 : weightTwoResidualDimension ≡ 276
weightTwoResidualDimensionIs276 = refl

dyadicBulkPlusWeightTwoResidualIs196884 :
  dyadicSymmetricBulk + weightTwoResidualDimension ≡ 196884
dyadicBulkPlusWeightTwoResidualIs196884 = refl

weightTwoResidualCharacterIs54 :
  nontrivialDyadicCorrection + 54 ≡ weightTwoInvariantCorrection
weightTwoResidualCharacterIs54 = refl

monsterResidualPlusConformalLineIsWeightTwoResidual :
  dyadicResidualDimension + 1 ≡ weightTwoResidualDimension
monsterResidualPlusConformalLineIsWeightTwoResidual = refl

------------------------------------------------------------------------
-- Uniform and ordered integer-valued probes.
--
-- Uniform probes see only total dimension.  The ordered probe sees the
-- centred positional defect:
--
--   (1,2,3) = 2(1,1,1) + (-1,0,1),
--
-- and because m1=m2, its displacement from the all-2 value is exactly 53.
------------------------------------------------------------------------

monsterAllOne : uniformOne monsterW3B ≡ 196883
monsterAllOne = refl

monsterAllTwo : uniformTwo monsterW3B ≡ 393766
monsterAllTwo = refl

monsterAllThree : uniformThree monsterW3B ≡ 590649
monsterAllThree = refl

monsterOneTwoThree : orderedOneTwoThree monsterW3B ≡ 393713
monsterOneTwoThree = refl

monsterThreeTwoOne : orderedThreeTwoOne monsterW3B ≡ 393819
monsterThreeTwoOne = refl

oneTwoThreePlusCharacterIsAllTwo :
  orderedOneTwoThree monsterW3B + 53 ≡ uniformTwo monsterW3B
oneTwoThreePlusCharacterIsAllTwo = refl

allTwoPlusCharacterIsThreeTwoOne :
  uniformTwo monsterW3B + 53 ≡ orderedThreeTwoOne monsterW3B
allTwoPlusCharacterIsThreeTwoOne = refl

monsterThreeSixNine : orderedThreeSixNine monsterW3B ≡ 1181139
monsterThreeSixNine = refl

threeTimesCharacterResidualIs159 : 3 * 53 ≡ 159
threeTimesCharacterResidualIs159 = refl

threeSixNinePlusThreeCharactersIsUniformSix :
  orderedThreeSixNine monsterW3B + 159
  ≡ 6 * phaseDimension monsterW3B
threeSixNinePlusThreeCharactersIsUniformSix = refl

record CrossTheoryBoundary : Set where
  constructor crossTheoryBoundary
  field
    exactSharedIntegerDecomposition : Bool
    exactSharedIntegerDecompositionIsTrue :
      exactSharedIntegerDecomposition ≡ true
    yangMillsSelectionExplainedByMonster : Bool
    yangMillsSelectionExplainedByMonsterIsFalse :
      yangMillsSelectionExplainedByMonster ≡ false
    monsterRepresentationIdentifiedWithYangMillsCarrier : Bool
    monsterRepresentationIdentifiedWithYangMillsCarrierIsFalse :
      monsterRepresentationIdentifiedWithYangMillsCarrier ≡ false

canonicalCrossTheoryBoundary : CrossTheoryBoundary
canonicalCrossTheoryBoundary =
  crossTheoryBoundary true refl false refl false refl
