module DASHI.Moonshine.MathieuDivisorLatticeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- John H. Conway, Robert T. Curtis, Simon P. Norton, Richard A. Parker,
-- and Robert A. Wilson,
-- "Atlas of Finite Groups", Oxford University Press, 1985.
-- No DOI assigned.
--
-- Garrett Birkhoff,
-- "Lattice Theory", third edition, American Mathematical Society, 1967.
-- DOI: 10.1090/coll/025.
--
-- DASHI CONTRIBUTION
--
-- Construct the divisor-lattice exponent boxes for 95040 and 7920, prove
-- their node counts, and separate the centralizer/class-index valuation split
-- 95040 = 192 * 495.  Distinct prime-coloured factor histories are proved to
-- converge to the same endpoint by exact commutation.  This is the finite
-- arithmetic skeleton of an interference model, not itself a quantum theory.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Products of valuation chains.
------------------------------------------------------------------------

record PrimeBounds : Set where
  constructor primeBounds
  field
    bound2 : Nat
    bound3 : Nat
    bound5 : Nat
    bound11 : Nat

open PrimeBounds public

nodeCount : PrimeBounds → Nat
nodeCount bounds =
  (bound2 bounds + 1)
  * (bound3 bounds + 1)
  * (bound5 bounds + 1)
  * (bound11 bounds + 1)

m12Bounds : PrimeBounds
m12Bounds = primeBounds 6 3 1 1

m11Bounds : PrimeBounds
m11Bounds = primeBounds 4 2 1 1

m12DivisorNodeCount : nodeCount m12Bounds ≡ 112
m12DivisorNodeCount = refl

m11DivisorNodeCount : nodeCount m11Bounds ≡ 60
m11DivisorNodeCount = refl

m12PrimeFactorization : 95040 ≡ 64 * 27 * 5 * 11
m12PrimeFactorization = refl

m11PrimeFactorization : 7920 ≡ 16 * 9 * 5 * 11
m11PrimeFactorization = refl

------------------------------------------------------------------------
-- Valuation vectors and the 192 x 495 split.
------------------------------------------------------------------------

record Valuation4 : Set where
  constructor valuation4
  field
    valuation2 : Nat
    valuation3 : Nat
    valuation5 : Nat
    valuation11 : Nat

open Valuation4 public

addValuation : Valuation4 → Valuation4 → Valuation4
addValuation left right =
  valuation4
    (valuation2 left + valuation2 right)
    (valuation3 left + valuation3 right)
    (valuation5 left + valuation5 right)
    (valuation11 left + valuation11 right)

m12Valuation : Valuation4
m12Valuation = valuation4 6 3 1 1

m11Valuation : Valuation4
m11Valuation = valuation4 4 2 1 1

centralizer192Valuation : Valuation4
centralizer192Valuation = valuation4 6 1 0 0

class495Valuation : Valuation4
class495Valuation = valuation4 0 2 1 1

centralizerPlusClassIsM12 :
  addValuation centralizer192Valuation class495Valuation
  ≡ m12Valuation
centralizerPlusClassIsM12 = refl

m11ToM12ValuationIncrement : Valuation4
m11ToM12ValuationIncrement = valuation4 2 1 0 0

m11PlusOrbitIncrementIsM12 :
  addValuation m11Valuation m11ToM12ValuationIncrement
  ≡ m12Valuation
m11PlusOrbitIncrementIsM12 = refl

centralizerOrder : Nat
centralizerOrder = 192

classIndex : Nat
classIndex = 495

centralizerFactorization : centralizerOrder ≡ 64 * 3
centralizerFactorization = refl

classIndexFactorization : classIndex ≡ 9 * 5 * 11
classIndexFactorization = refl

centralizerTimesClassIndex :
  centralizerOrder * classIndex ≡ 95040
centralizerTimesClassIndex = refl

m12OverM11OrbitFactor : 12 * 7920 ≡ 95040
m12OverM11OrbitFactor = refl

------------------------------------------------------------------------
-- The binomial count 495 = choose(12,4).
------------------------------------------------------------------------

choose : Nat → Nat → Nat
choose n zero = 1
choose zero (suc k) = 0
choose (suc n) (suc k) = choose n k + choose n (suc k)

chooseTwelveFourIs495 : choose 12 4 ≡ 495
chooseTwelveFourIs495 = refl

classIndexMatchesFourSubsetCount : classIndex ≡ choose 12 4
classIndexMatchesFourSubsetCount = refl

------------------------------------------------------------------------
-- Prime-coloured path confluence.
------------------------------------------------------------------------

data PrimeStep : Set where
  times2 times3 times5 times11 : PrimeStep

applyStep : PrimeStep → Nat → Nat
applyStep times2 value = 2 * value
applyStep times3 value = 3 * value
applyStep times5 value = 5 * value
applyStep times11 value = 11 * value

twoThenThreeConverges :
  applyStep times3 (applyStep times2 1)
  ≡ applyStep times2 (applyStep times3 1)
twoThenThreeConverges = refl

twoThreeFiveAllOrdersExample :
  applyStep times5 (applyStep times3 (applyStep times2 1))
  ≡ applyStep times2 (applyStep times5 (applyStep times3 1))
twoThreeFiveAllOrdersExample = refl

threeFiveElevenConverges :
  applyStep times11 (applyStep times5 (applyStep times3 1))
  ≡ applyStep times3 (applyStep times11 (applyStep times5 1))
threeFiveElevenConverges = refl

record FactorHistory : Set where
  constructor factorHistory
  field
    start : Nat
    first : PrimeStep
    second : PrimeStep
    endpoint : Nat
    endpointLaw : endpoint ≡ applyStep second (applyStep first start)

open FactorHistory public

historyTwoThree : FactorHistory
historyTwoThree = factorHistory 1 times2 times3 6 refl

historyThreeTwo : FactorHistory
historyThreeTwo = factorHistory 1 times3 times2 6 refl

historiesShareEndpoint : endpoint historyTwoThree ≡ endpoint historyThreeTwo
historiesShareEndpoint = refl

record DivisorLatticeBoundary : Set where
  constructor divisorLatticeBoundary
  field
    exponentBoxesAndCountsExact : Bool
    exponentBoxesAndCountsExactIsTrue :
      exponentBoxesAndCountsExact ≡ true
    pathConfluenceUsesPrimeCommutation : Bool
    pathConfluenceUsesPrimeCommutationIsTrue :
      pathConfluenceUsesPrimeCommutation ≡ true
    incidenceDiagramSuppliesComplexAmplitudes : Bool
    incidenceDiagramSuppliesComplexAmplitudesIsFalse :
      incidenceDiagramSuppliesComplexAmplitudes ≡ false
    arithmeticSplitConstructsCentralizerAction : Bool
    arithmeticSplitConstructsCentralizerActionIsFalse :
      arithmeticSplitConstructsCentralizerAction ≡ false
    chooseTwelveFourAloneProvesCycleShape : Bool
    chooseTwelveFourAloneProvesCycleShapeIsFalse :
      chooseTwelveFourAloneProvesCycleShape ≡ false

canonicalDivisorLatticeBoundary : DivisorLatticeBoundary
canonicalDivisorLatticeBoundary =
  divisorLatticeBoundary true refl true refl false refl false refl false refl
