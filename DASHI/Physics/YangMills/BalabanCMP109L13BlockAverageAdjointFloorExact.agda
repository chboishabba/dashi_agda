module DASHI.Physics.YangMills.BalabanCMP109L13BlockAverageAdjointFloorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Compute the normalized L=13 block-average adjoint on the literal
-- 342732-coordinate state carrier.  A multiplier has 3 Lie coordinates times
-- 4 positive directions.  The normalized block average uses weight 1/28561,
-- so its adjoint is constant over the 28561 sites.  Exact finite Fubini gives
--
--   ||Q* lambda||^2 = 28561 * (1/28561)^2 ||lambda||^2
--                      = (1/28561) ||lambda||^2.
--
-- This is the source-scale replacement for the block-average row floor in the
-- reduced combined Gram argument; no side-four state or dimension enters.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (List; []; _∷_; length)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Nat.Base as N
open import Data.Product using (_,_)
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact
open import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact using
  (sumRationalConstant)
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanPhysicalBlockAverageConstraintMatrixExact as BlockAverage
import DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact as Side13
import DASHI.Physics.YangMills.BalabanPath13SU2RationalMatrixDimensionExact as Dimension
import DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalAdmissibleRepositoryScaleExact as Minimal

Row : Set
Row = BlockAverage.SelectedBlockAverageRow

RowVector : Set
RowVector = Row → ℚ

State : Set
State = Physical.PhysicalSU2Coordinate Side13.side13

StateVector : Set
StateVector = State → ℚ

rowNormSq : RowVector → ℚ
rowNormSq multiplier =
  sumRational BlockAverage.selectedBlockAverageRows
    (λ row → sq (multiplier row))

normalizedBlockAverageAdjoint : RowVector → StateVector
normalizedBlockAverageAdjoint multiplier
    (pair coordinate (pair axis site)) =
  Minimal.siteWeightℚ * multiplier (pair coordinate axis)

stateNormSq : StateVector → ℚ
stateNormSq = Physical.physicalSU2CoordinateNormSq

siteWeightSquareTimesVolume : ∀ value →
  Dimension.path13PhysicalMatrixDimension -- dummy argument prevents hidden numeral reduction drift
    ≡ Dimension.path13PhysicalMatrixDimension →
  (+ 28561 / 1) * sq Minimal.siteWeightℚ * value
  ≡ Minimal.siteWeightℚ * value
siteWeightSquareTimesVolume value dimensionStable = ℚRing.solve-∀ value

siteConstantSquareSum : ∀ coordinate axis multiplier →
  sumRational (physicalBlockSites Side13.side13)
    (λ site → sq (Minimal.siteWeightℚ * multiplier (pair coordinate axis)))
  ≡ Minimal.siteWeightℚ * sq (multiplier (pair coordinate axis))
siteConstantSquareSum coordinate axis multiplier =
  trans
    (sumRationalConstant
      (physicalBlockSites Side13.side13)
      (sq (Minimal.siteWeightℚ * multiplier (pair coordinate axis))))
    (trans
      (cong
        (λ count →
          natAsRational count
          * sq (Minimal.siteWeightℚ * multiplier (pair coordinate axis)))
        (siteListLengthExact))
      (ℚRing.solve-∀ (multiplier (pair coordinate axis))))
  where
  siteListLengthExact :
    length (physicalBlockSites Side13.side13) ≡ 28561
  siteListLengthExact = Dimension.siteCountExact

normalizedAdjointNormExact : ∀ multiplier →
  stateNormSq (normalizedBlockAverageAdjoint multiplier)
  ≡ Minimal.siteWeightℚ * rowNormSq multiplier
normalizedAdjointNormExact multiplier =
  trans
    (sumCartesian
      Physical.lieCoordinates3
      (Physical.physicalBondCells Side13.side13)
      (λ stateCoordinate →
        sq (normalizedBlockAverageAdjoint multiplier stateCoordinate)))
    (trans
      (sumRationalCong
        Physical.lieCoordinates3
        (λ coordinate →
          sumRational (Physical.physicalBondCells Side13.side13)
            (λ cell →
              sq (normalizedBlockAverageAdjoint multiplier
                (pair coordinate cell))))
        (λ coordinate →
          sumRational (allCyclicIndices four)
            (λ axis →
              Minimal.siteWeightℚ * sq (multiplier (pair coordinate axis))))
        (λ coordinate →
          trans
            (sumCartesian
              (allCyclicIndices four)
              (physicalBlockSites Side13.side13)
              (λ cell →
                sq (normalizedBlockAverageAdjoint multiplier
                  (pair coordinate cell))))
            (sumRationalCong
              (allCyclicIndices four)
              (λ axis →
                sumRational (physicalBlockSites Side13.side13)
                  (λ site →
                    sq (Minimal.siteWeightℚ
                      * multiplier (pair coordinate axis))))
              (λ axis →
                Minimal.siteWeightℚ * sq (multiplier (pair coordinate axis)))
              (λ axis → siteConstantSquareSum coordinate axis multiplier))))
      (trans
        (sumRationalCong
          Physical.lieCoordinates3
          (λ coordinate →
            sumRational (allCyclicIndices four)
              (λ axis →
                Minimal.siteWeightℚ * sq (multiplier (pair coordinate axis))))
          (λ coordinate →
            Minimal.siteWeightℚ
              * sumRational (allCyclicIndices four)
                  (λ axis → sq (multiplier (pair coordinate axis))))
          (λ coordinate →
            sumRationalScale
              Minimal.siteWeightℚ
              (allCyclicIndices four)
              (λ axis → sq (multiplier (pair coordinate axis)))))
        (sumRationalScale
          Minimal.siteWeightℚ
          Physical.lieCoordinates3
          (λ coordinate →
            sumRational (allCyclicIndices four)
              (λ axis → sq (multiplier (pair coordinate axis)))))))

normalizedBlockAverageAdjointFloor : ∀ multiplier →
  Minimal.siteWeightℚ * rowNormSq multiplier
  ≤ stateNormSq (normalizedBlockAverageAdjoint multiplier)
normalizedBlockAverageAdjointFloor multiplier
  rewrite normalizedAdjointNormExact multiplier = ℚP.≤-refl

cmp109L13NormalizedBlockAverageAdjointExactLevel : ProofLevel
cmp109L13NormalizedBlockAverageAdjointExactLevel = machineChecked

cmp109L13NormalizedBlockAverageAdjointFloorLevel : ProofLevel
cmp109L13NormalizedBlockAverageAdjointFloorLevel = machineChecked

------------------------------------------------------------------------
-- Multi-block flat Eq.(120). The old one-block row norm above is correct
-- when the length-13 segment wraps all the way around the fine torus.
-- On a coarse direction with arbitrary cyclic size, the true coefficient
-- is the convolution of two length-13 boxes, not the constant block row.
-- Wilson / Bałaban CMP98, Eq.(119)--(121); exact triangular count below.
------------------------------------------------------------------------

smallRange : Nat → List Nat
smallRange zero = []
smallRange (suc n) = n ∷ smallRange n

natIndicator : Nat → Nat → Nat
natIndicator zero zero = 1
natIndicator zero (suc _) = 0
natIndicator (suc _) zero = 0
natIndicator (suc a) (suc b) = natIndicator a b

sumNat : List Nat → (Nat → Nat) → Nat
sumNat [] f = 0
sumNat (x ∷ xs) f = f x N.+ sumNat xs f

axisSegmentCount : Nat → Nat
axisSegmentCount k =
  sumNat (smallRange 13) (λ x →
    sumNat (smallRange 13) (λ j → natIndicator (x N.+ j) k))

centreCountExact : axisSegmentCount 6 ≡ 7
centreCountExact = refl

nextCentreCountExact : axisSegmentCount 19 ≡ 6
nextCentreCountExact = refl

diagonalCount : Nat
diagonalCount = sumNat (smallRange 25)
  (λ k → axisSegmentCount k N.* axisSegmentCount k)

adjacentCount : Nat
adjacentCount = sumNat (smallRange 25)
  (λ k → axisSegmentCount k N.* axisSegmentCount (k N.+ 13))

diagonalCountExact : diagonalCount ≡ 1469
diagonalCountExact = refl

adjacentCountExact : adjacentCount ≡ 364
adjacentCountExact = refl

-- The transverse box contributes 13^3, and the product row denominator
-- is (13^5)^2. These are the exact 3D-transverse normalized coefficients.
multiBlockGramDiagonal multiBlockGramAdjacent multiBlockGramFloor : ℚ
multiBlockGramDiagonal = + 113 / 4826809
multiBlockGramAdjacent = + 28 / 4826809
multiBlockGramFloor = + 57 / 4826809

diagonalNormalizationExact :
  (+ 1469 / 62748517) ≡ multiBlockGramDiagonal
diagonalNormalizationExact = refl

adjacentNormalizationExact :
  (+ 364 / 62748517) ≡ multiBlockGramAdjacent
adjacentNormalizationExact = refl

cycleEdgesFrom : ℚ → ℚ → List ℚ → List L2.Pair
cycleEdgesFrom first current [] = (current , first) ∷ []
cycleEdgesFrom first current (next ∷ rest) =
  (current , next) ∷ cycleEdgesFrom first next rest

cycleEdges : List ℚ → List L2.Pair
cycleEdges [] = []
cycleEdges (first ∷ rest) = cycleEdgesFrom first first rest

sumSquares : List ℚ → ℚ
sumSquares [] = 0ℚ
sumSquares (x ∷ xs) = L2.square x + sumSquares xs

cycleEdgesLeft : ∀ first current rest →
  L2.leftNormSquared (cycleEdgesFrom first current rest)
    ≡ L2.square current + sumSquares rest
cycleEdgesLeft first current [] = refl
cycleEdgesLeft first current (next ∷ rest)
  rewrite cycleEdgesLeft first next rest = refl

cycleEdgesRight : ∀ first current rest →
  L2.rightNormSquared (cycleEdgesFrom first current rest)
    ≡ sumSquares rest + L2.square first
cycleEdgesRight first current [] =
  ℚRing.solve-∀ (L2.square first)
cycleEdgesRight first current (next ∷ rest)
  rewrite cycleEdgesRight first next rest =
    sym (ℚP.+-assoc (L2.square next) (sumSquares rest) (L2.square first))

cycleEdgesEqualNorm : ∀ values →
  L2.leftNormSquared (cycleEdges values)
    ≡ L2.rightNormSquared (cycleEdges values)
cycleEdgesEqualNorm [] = refl
cycleEdgesEqualNorm (first ∷ rest)
  rewrite cycleEdgesLeft first first rest | cycleEdgesRight first first rest =
    ℚP.+-comm (L2.square first) (sumSquares rest)

pairPlusSquares : List L2.Pair → ℚ
pairPlusSquares [] = 0ℚ
pairPlusSquares ((x , y) ∷ rest) =
  L2.square (x + y) + pairPlusSquares rest

pairPlusSquaresNonnegative : ∀ pairs → 0ℚ ≤ pairPlusSquares pairs
pairPlusSquaresNonnegative [] = ℚP.≤-refl
pairPlusSquaresNonnegative ((x , y) ∷ rest) =
  L2.addNonnegative
    (L2.squareNonnegative (x + y)) (pairPlusSquaresNonnegative rest)

pairPlusSquaresExpansion : ∀ pairs →
  pairPlusSquares pairs ≡
    L2.leftNormSquared pairs + L2.rightNormSquared pairs
      + (+ 2 / 1) * L2.pairDot pairs
pairPlusSquaresExpansion [] = refl
pairPlusSquaresExpansion ((x , y) ∷ rest)
  rewrite pairPlusSquaresExpansion rest =
    ℚRing.solve-∀ x y (L2.leftNormSquared rest)
      (L2.rightNormSquared rest) (L2.pairDot rest)

cyclicMultiBlockGramForm : List ℚ → ℚ
cyclicMultiBlockGramForm values =
  multiBlockGramDiagonal * L2.leftNormSquared (cycleEdges values)
  + (+ 2 / 1) * multiBlockGramAdjacent * L2.pairDot (cycleEdges values)

-- No assumption on the number of coarse sites. The aligned shift is
-- the actual cyclic edge list, including the one-site/two-site wraps.
cyclicMultiBlockGramLower : ∀ values →
  multiBlockGramFloor * L2.leftNormSquared (cycleEdges values)
    ≤ cyclicMultiBlockGramForm values
cyclicMultiBlockGramLower values =
  let
    pairs = cycleEdges values
    l = L2.leftNormSquared pairs
    p = L2.pairDot pairs
    same = cycleEdgesEqualNorm values
    scaledNN = Norm.scaleNonnegative multiBlockGramAdjacent
      (ℚP.nonNegative⁻¹ multiBlockGramAdjacent)
      (pairPlusSquaresNonnegative pairs)
    expanded = subst
      (λ z → multiBlockGramAdjacent * 0ℚ ≤ multiBlockGramAdjacent * z)
      (pairPlusSquaresExpansion pairs) scaledNN
    replaced = subst
      (λ rr → multiBlockGramAdjacent * 0ℚ ≤
        multiBlockGramAdjacent * (l + rr + (+ 2 / 1) * p))
      (sym same) expanded
    gap : multiBlockGramAdjacent * (l + l + (+ 2 / 1) * p)
      ≡ cyclicMultiBlockGramForm values - multiBlockGramFloor * l
    gap = ℚRing.solve-∀ l p
  in Norm.nonnegativeDifferenceImpliesBelow
       (subst (λ z → 0ℚ ≤ z) gap
         (subst
           (λ z → z ≤ multiBlockGramAdjacent * (l + l + (+ 2 / 1) * p))
           (ℚP.*-zeroʳ multiBlockGramAdjacent) replaced))
