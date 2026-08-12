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
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

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
