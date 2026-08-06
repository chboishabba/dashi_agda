module DASHI.Physics.Common.ReducedModeProjectionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Fan R. K. Chung,
-- "Spectral Graph Theory", CBMS Regional Conference Series in Mathematics
-- 92, American Mathematical Society, 1997.
-- DOI: 10.1090/cbms/092.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Construct the smallest exact rational prototype of
--
--   field = invariant mode + mean-zero fluctuation,
--
-- prove orthogonality and norm splitting, and keep the dimension count
--
--   54 = 1 + 53
--
-- in the same typed module.  The two-site projector is a finite algebraic
-- prototype; it is not the physical torus Laplacian, a gauge quotient, or a
-- proof that the reduced 53-carrier is an irreducible representation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; true; false)
open import Data.Nat.Base using (ℕ; _+_) renaming (ℕ to Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong₂)

half : ℚ
half = + 1 / 2

record PairField : Set where
  constructor pairField
  field
    left : ℚ
    right : ℚ

open PairField public

pairAdd : PairField → PairField → PairField
pairAdd first second =
  pairField
    (left first + left second)
    (right first + right second)

constantPart : PairField → PairField
constantPart field =
  let average = half * (left field + right field)
  in pairField average average

meanZeroPart : PairField → PairField
meanZeroPart field =
  pairField
    (half * (left field - right field))
    (half * (right field - left field))

fieldReconstructsFromConstantAndMeanZero :
  (field : PairField) →
  pairAdd (constantPart field) (meanZeroPart field) ≡ field
fieldReconstructsFromConstantAndMeanZero (pairField x y) =
  cong₂ pairField
    (ℚRing.solve-∀ x y)
    (ℚRing.solve-∀ x y)

meanZeroPartHasZeroSum :
  (field : PairField) →
  left (meanZeroPart field) + right (meanZeroPart field) ≡ 0ℚ
meanZeroPartHasZeroSum (pairField x y) =
  ℚRing.solve-∀ x y

constantPartHasEqualCoordinates :
  (field : PairField) →
  left (constantPart field) ≡ right (constantPart field)
constantPartHasEqualCoordinates field = refl

meanZeroPartKillsConstantField :
  (value : ℚ) →
  meanZeroPart (pairField value value) ≡ pairField 0ℚ 0ℚ
meanZeroPartKillsConstantField value =
  cong₂ pairField
    (ℚRing.solve-∀ value)
    (ℚRing.solve-∀ value)

meanZeroProjectionIdempotent :
  (field : PairField) →
  meanZeroPart (meanZeroPart field) ≡ meanZeroPart field
meanZeroProjectionIdempotent (pairField x y) =
  cong₂ pairField
    (ℚRing.solve-∀ x y)
    (ℚRing.solve-∀ x y)

constantProjectionIdempotent :
  (field : PairField) →
  constantPart (constantPart field) ≡ constantPart field
constantProjectionIdempotent (pairField x y) =
  cong₂ pairField
    (ℚRing.solve-∀ x y)
    (ℚRing.solve-∀ x y)

dot : PairField → PairField → ℚ
dot first second =
  left first * left second + right first * right second

normSq : PairField → ℚ
normSq field = dot field field

constantMeanZeroOrthogonal :
  (field : PairField) →
  dot (constantPart field) (meanZeroPart field) ≡ 0ℚ
constantMeanZeroOrthogonal (pairField x y) =
  ℚRing.solve-∀ x y

constantMeanZeroNormSplit :
  (field : PairField) →
  normSq field
  ≡ normSq (constantPart field) + normSq (meanZeroPart field)
constantMeanZeroNormSplit (pairField x y) =
  ℚRing.solve-∀ x y

record ReducedModeCount : Set where
  constructor reducedModeCount
  field
    totalModes : Nat
    invariantModes : Nat
    fluctuationModes : Nat
    totalSplits : totalModes ≡ invariantModes + fluctuationModes

open ReducedModeCount public

sixByNineReducedModeCount : ReducedModeCount
sixByNineReducedModeCount = reducedModeCount 54 1 53 refl

sixByNineIsInvariantPlusReduced :
  totalModes sixByNineReducedModeCount
  ≡ invariantModes sixByNineReducedModeCount
    + fluctuationModes sixByNineReducedModeCount
sixByNineIsInvariantPlusReduced = totalSplits sixByNineReducedModeCount

data ReducedModeApplication : Set where
  DASHISixByNineFluctuation : ReducedModeApplication
  navierStokesNonzeroFourierMode : ReducedModeApplication
  yangMillsGaugeFixedFluctuation : ReducedModeApplication
  graphDiffusionPositiveMode : ReducedModeApplication

record ReducedModeBoundary : Set where
  constructor reducedModeBoundary
  field
    commonModeRemovalAlgebraIsReusable : Bool
    commonModeRemovalAlgebraIsReusableIsTrue :
      commonModeRemovalAlgebraIsReusable ≡ true
    commonModeCountIdentifiesPhysicalOperators : Bool
    commonModeCountIdentifiesPhysicalOperatorsIsFalse :
      commonModeCountIdentifiesPhysicalOperators ≡ false

canonicalReducedModeBoundary : ReducedModeBoundary
canonicalReducedModeBoundary =
  reducedModeBoundary true refl false refl
