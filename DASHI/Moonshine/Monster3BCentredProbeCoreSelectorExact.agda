module DASHI.Moonshine.Monster3BCentredProbeCoreSelectorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine", Bulletin of the London Mathematical Society 11
-- (1979), 308--339. DOI: 10.1112/blms/11.3.308.
--
-- R. W. Barraclough and R. A. Wilson,
-- "The Character Table of a Maximal Subgroup of the Monster",
-- LMS Journal of Computation and Mathematics 10 (2007), 161--175.
-- DOI: 10.1112/S1461157000001352.
--
-- DASHI CONTRIBUTION
--
-- Replace the separate 1-2-3, 3-2-1 and 3-6-9 observations by one
-- division-free centred-probe theorem.  Separate the canonical maximal
-- C3-regular core 65610 from the optional dyadic selector 65536, and make the
-- resulting S3 -> S2 symmetry reduction explicit.  No Monster-action theorem
-- selecting the dyadic core is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Moonshine.Monster3BCyclicFourierDyadicBridgeExact as Fourier

record RationalTriple : Set where
  constructor triple
  field
    first : ℚ
    second : ℚ
    third : ℚ

open RationalTriple public

weightedProbe : RationalTriple → RationalTriple → ℚ
weightedProbe weights values =
  first weights * first values
  + second weights * second values
  + third weights * third values

augmentation : RationalTriple → ℚ
augmentation values = first values + second values + third values

balancedDefectVector : ℚ → ℚ → RationalTriple
balancedDefectVector bulk defect = triple (bulk + defect) bulk bulk

weightSum : RationalTriple → ℚ
weightSum = augmentation

centredProbeDefectFactorization :
  ∀ weights bulk defect →
  (+ 3 / 1) * weightedProbe weights (balancedDefectVector bulk defect)
  ≡ weightSum weights * augmentation (balancedDefectVector bulk defect)
    + defect
      * ((+ 3 / 1) * first weights - weightSum weights)
centredProbeDefectFactorization
    (triple w0 w1 w2) bulk defect =
  ℚRing.solve-∀ w0 w1 w2 bulk defect

oneTwoThree threeTwoOne threeSixNine : RationalTriple
oneTwoThree = triple (+ 1 / 1) (+ 2 / 1) (+ 3 / 1)
threeTwoOne = triple (+ 3 / 1) (+ 2 / 1) (+ 1 / 1)
threeSixNine = triple (+ 3 / 1) (+ 6 / 1) (+ 9 / 1)

monsterMultiplicityQ : RationalTriple
monsterMultiplicityQ =
  triple (+ 65663 / 1) (+ 65610 / 1) (+ 65610 / 1)

weightTwoMultiplicityQ : RationalTriple
weightTwoMultiplicityQ =
  triple (+ 65664 / 1) (+ 65610 / 1) (+ 65610 / 1)

monsterOneTwoThreeCentred :
  weightedProbe oneTwoThree monsterMultiplicityQ + (+ 53 / 1)
  ≡ (+ 2 / 1) * augmentation monsterMultiplicityQ
monsterOneTwoThreeCentred = ℚRing.solve []

monsterThreeTwoOneCentred :
  (+ 2 / 1) * augmentation monsterMultiplicityQ + (+ 53 / 1)
  ≡ weightedProbe threeTwoOne monsterMultiplicityQ
monsterThreeTwoOneCentred = ℚRing.solve []

monsterThreeSixNineCentred :
  weightedProbe threeSixNine monsterMultiplicityQ + (+ 159 / 1)
  ≡ (+ 6 / 1) * augmentation monsterMultiplicityQ
monsterThreeSixNineCentred = ℚRing.solve []

weightTwoOneTwoThreeCentred :
  weightedProbe oneTwoThree weightTwoMultiplicityQ + (+ 54 / 1)
  ≡ (+ 2 / 1) * augmentation weightTwoMultiplicityQ
weightTwoOneTwoThreeCentred = ℚRing.solve []

------------------------------------------------------------------------
-- Canonical and dyadic uniform cores.
------------------------------------------------------------------------

maximalRegularCore dyadicUniformCore : Nat
maximalRegularCore = 65610
dyadicUniformCore = 65536

maximalRegularResidual : Fourier.ThreePhaseMultiplicity
maximalRegularResidual = Fourier.threePhaseMultiplicity 53 0 0

dyadicResidualW : Fourier.ThreePhaseMultiplicity
dyadicResidualW = Fourier.threePhaseMultiplicity 127 74 74

dyadicResidualWeightTwo : Fourier.ThreePhaseMultiplicity
dyadicResidualWeightTwo = Fourier.threePhaseMultiplicity 128 74 74

maximalCoreReconstructsMonsterInvariant :
  maximalRegularCore + Fourier.invariant maximalRegularResidual
  ≡ Fourier.invariant Fourier.monsterW3B
maximalCoreReconstructsMonsterInvariant = refl

maximalCoreReconstructsMonsterZeta :
  maximalRegularCore + Fourier.zeta maximalRegularResidual
  ≡ Fourier.zeta Fourier.monsterW3B
maximalCoreReconstructsMonsterZeta = refl

dyadicCoreReconstructsMonsterInvariant :
  dyadicUniformCore + Fourier.invariant dyadicResidualW
  ≡ Fourier.invariant Fourier.monsterW3B
dyadicCoreReconstructsMonsterInvariant = refl

dyadicCoreReconstructsMonsterZeta :
  dyadicUniformCore + Fourier.zeta dyadicResidualW
  ≡ Fourier.zeta Fourier.monsterW3B
dyadicCoreReconstructsMonsterZeta = refl

dyadicCoreReconstructsWeightTwoInvariant :
  dyadicUniformCore + Fourier.invariant dyadicResidualWeightTwo
  ≡ Fourier.invariant Fourier.moonshineWeightTwo3B
dyadicCoreReconstructsWeightTwoInvariant = refl

dyadicUniformSubtotal : Nat
dyadicUniformSubtotal = 3 * dyadicUniformCore

dyadicUniformSubtotalIs196608 :
  dyadicUniformSubtotal ≡ 196608
dyadicUniformSubtotalIs196608 = refl

maximalUniformSubtotal : Nat
maximalUniformSubtotal = 3 * maximalRegularCore

maximalUniformSubtotalIs196830 :
  maximalUniformSubtotal ≡ 196830
maximalUniformSubtotalIs196830 = refl

------------------------------------------------------------------------
-- The nontrivial sectors form the residual exchange symmetry.
------------------------------------------------------------------------

swapNontrivial :
  Fourier.ThreePhaseMultiplicity → Fourier.ThreePhaseMultiplicity
swapNontrivial values =
  Fourier.threePhaseMultiplicity
    (Fourier.invariant values)
    (Fourier.zetaSquared values)
    (Fourier.zeta values)

swapNontrivialMonsterFixed :
  swapNontrivial Fourier.monsterW3B ≡ Fourier.monsterW3B
swapNontrivialMonsterFixed = refl

swapNontrivialMaximalResidualFixed :
  swapNontrivial maximalRegularResidual ≡ maximalRegularResidual
swapNontrivialMaximalResidualFixed = refl

swapNontrivialDyadicResidualFixed :
  swapNontrivial dyadicResidualW ≡ dyadicResidualW
swapNontrivialDyadicResidualFixed = refl

record CoreSelectionBoundary : Set where
  constructor coreSelectionBoundary
  field
    maximalRegularCoreCanonicalFromMultiplicity : Bool
    maximalRegularCoreCanonicalFromMultiplicityIsTrue :
      maximalRegularCoreCanonicalFromMultiplicity ≡ true

    dyadicCoreIsExactRefinement : Bool
    dyadicCoreIsExactRefinementIsTrue :
      dyadicCoreIsExactRefinement ≡ true

    dyadicCoreCanonicallySelectedByMonsterAction : Bool
    dyadicCoreCanonicallySelectedByMonsterActionIsFalse :
      dyadicCoreCanonicallySelectedByMonsterAction ≡ false

    equalNontrivialSectorsPreserveExchangeSymmetry : Bool
    equalNontrivialSectorsPreserveExchangeSymmetryIsTrue :
      equalNontrivialSectorsPreserveExchangeSymmetry ≡ true

canonicalCoreSelectionBoundary : CoreSelectionBoundary
canonicalCoreSelectionBoundary =
  coreSelectionBoundary true refl true refl false refl true refl
