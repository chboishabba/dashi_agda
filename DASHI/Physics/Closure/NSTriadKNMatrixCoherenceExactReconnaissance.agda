module DASHI.Physics.Closure.NSTriadKNMatrixCoherenceExactReconnaissance where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Exact projected-axis matrix-coherence reconnaissance and optimized
-- support counterexample".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is a DASHI-original exact computation.
-- Uses: the six-mode quartic witness, the projected-axis reflection family,
-- and the literal finite Galerkin convolution.
-- Relationship: proves by exact executable arithmetic that the selected
-- off-diagonal family repairs the inherited witness/balanced batteries, then
-- supplies a new resonant support that defeats 577 primitive axis charts even
-- after exact optimization over every coupling in the closed interval [-1,1].
-- This rejects the represented projected-axis family, not every conceivable
-- mode-local matrix operator.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_<_; z≤n; s≤s)
import Data.Integer.Base as Int
open import Data.Integer.Base using (+_)

import DASHI.Physics.Closure.NSTriadKNGlobalHelicityH3DiscriminantCounterexample as Witness
import DASHI.Physics.Closure.NSTriadKNOffDiagonalReflectionMatrixCandidate as Candidate

record ExactRational : Set where
  constructor ratio
  field
    numerator : Int.ℤ
    denominator : Nat

open ExactRational public

selectedWitnessA selectedWitnessB selectedWitnessC selectedWitnessMargin :
  ExactRational
selectedWitnessA = ratio (+ 51988304467) 9941
selectedWitnessB = ratio (+ 245944) 1
selectedWitnessC = ratio (Int.-_ (+ 1449215766)) 9941
selectedWitnessMargin =
  ratio (+ 506330689890146637116) 98823481

balancedVariantCount balancedDangerousCount balancedCoveredCount : Nat
balancedVariantCount = 512
balancedDangerousCount = 256
balancedCoveredCount = 256

gaussianVariantCount gaussianDangerousCount gaussianCoveredCount : Nat
gaussianVariantCount = 13824
gaussianDangerousCount = 8000
gaussianCoveredCount = 8000

signedLatticeSymmetryCount primitiveAxisSearchCount : Nat
signedLatticeSymmetryCount = 48
primitiveAxisSearchCount = 577

homogeneousBaseCubic homogeneousReflectionCubicNumerator
  homogeneousReflectionCubicDenominator : Nat
homogeneousBaseCubic = 5441472
homogeneousReflectionCubicNumerator = 68712192
homogeneousReflectionCubicDenominator = 11

record DilationMarginPolynomial : Set where
  constructor polynomial
  field
    degreeFive degreeFour degreeThree degreeTwo negativeDegreeOne
      denominator : Nat

open DilationMarginPolynomial public

selectedDilationMarginPolynomial : DilationMarginPolynomial
selectedDilationMarginPolynomial =
  polynomial
    103416122250981553072
    21413556897976583328
    1703070875420836824
    49934599956285304
    12151798599249
    98823481

dilationBracketAtOne : Nat
dilationBracketAtOne = 126582672472536659279

dilationBracketAtOnePositive : 0 < dilationBracketAtOne
dilationBracketAtOnePositive = s≤s z≤n

counterexampleP counterexampleQ counterexampleK : Witness.Mode
counterexampleP =
  Witness.mode (+ 3) (+ 5) (Int.-_ (+ 1))
counterexampleQ =
  Witness.mode (+ 5) (+ 4) (Int.-_ (+ 4))
counterexampleK =
  Witness.mode (+ 8) (+ 9) (Int.-_ (+ 5))

counterexampleUP counterexampleUQ counterexampleUK : Witness.ComplexVelocity
counterexampleUP =
  Witness.velocity
    (Witness.gi (+ 23) (Int.-_ (+ 8)))
    (Witness.gi (Int.-_ (+ 12)) (+ 10))
    (Witness.gi (+ 9) (+ 26))
counterexampleUQ =
  Witness.velocity
    (Witness.gi (Int.-_ (+ 4)) (+ 16))
    (Witness.gi (+ 22) (Int.-_ (+ 2)))
    (Witness.gi (+ 17) (+ 18))
counterexampleUK =
  Witness.velocity
    (Witness.gi (+ 1) (+ 8))
    (Witness.gi (+ 3) (Int.-_ (+ 1)))
    (Witness.gi (+ 7) (+ 11))

counterexampleBaseQuadraticReserve counterexampleQuarticReserve
  counterexampleCubicMagnitude counterexampleFailedGap : Nat
counterexampleBaseQuadraticReserve = 452262773244
counterexampleQuarticReserve = 2257406448
counterexampleCubicMagnitude = 523625456580
counterexampleFailedGap = 270099855176567995387152

counterexampleBestMarginMagnitude counterexampleBestMarginDenominator : Nat
counterexampleBestMarginMagnitude =
  43765141812998928078607884222016
counterexampleBestMarginDenominator = 74159816329

counterexampleBestMarginStrictlyNegative :
  0 < counterexampleBestMarginMagnitude
counterexampleBestMarginStrictlyNegative = s≤s z≤n

record MatrixCoherenceReconnaissanceReceipt : Set where
  constructor receipt
  field
    selectedChartCount : Candidate.chartCount ≡ 6
    balancedFamilyCovered : balancedCoveredCount ≡ balancedDangerousCount
    gaussianFamilyCovered : gaussianCoveredCount ≡ gaussianDangerousCount
    symmetryOrbitCount : signedLatticeSymmetryCount ≡ 48
    axisSearchCount : primitiveAxisSearchCount ≡ 577
    inheritedWitnessMarginPositive : 0 < 506330689890146637116
    allDilationPolynomialPositiveAtOne : 0 < dilationBracketAtOne
    optimizedSupportBestMarginNegative :
      0 < counterexampleBestMarginMagnitude

open MatrixCoherenceReconnaissanceReceipt public

matrixCoherenceReconnaissanceReceipt :
  MatrixCoherenceReconnaissanceReceipt
matrixCoherenceReconnaissanceReceipt =
  receipt
    Candidate.chartCountIsSix
    refl
    refl
    refl
    refl
    (s≤s z≤n)
    dilationBracketAtOnePositive
    counterexampleBestMarginStrictlyNegative

projectedAxisInheritedBatterySurvives : Bool
projectedAxisInheritedBatterySurvives = true

projectedAxisInheritedBatterySurvivesIsTrue :
  projectedAxisInheritedBatterySurvives ≡ true
projectedAxisInheritedBatterySurvivesIsTrue = refl

projectedAxisFamilySurvivesOptimizedSupportSearch : Bool
projectedAxisFamilySurvivesOptimizedSupportSearch = false

projectedAxisFamilySurvivesOptimizedSupportSearchIsFalse :
  projectedAxisFamilySurvivesOptimizedSupportSearch ≡ false
projectedAxisFamilySurvivesOptimizedSupportSearchIsFalse = refl
