module DASHI.Physics.YangMills.BalabanP33PhysicalResidualHalfContractionAtCollar21Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics, 1995 reprint.
-- DOI: 10.1007/978-3-642-66282-9.
--
-- DASHI CONTRIBUTION
--
-- Consume exactly one remaining physical estimate--the weighted entry estimate
-- for R=I-HG* at collar M=21--and construct the repository's literal finite
-- half-contraction object.  All support, radius and scalar constants are fixed:
--
--   N=3072, r0=8, s=2, s^r0=256,
--   epsilon=2^-21=1/2097152,
--   N epsilon s^r0=3/8 <= 1/2.
--
-- No second row-sum or operator-norm assumption is requested.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSupportCountHalfExact as Support
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedRowSumContractionExact as Row
import DASHI.Physics.YangMills.BalabanP33LiteralResidualKernelNumericalCalibrationExact as Calibration
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums

supportCoefficientAtCollar21 : ℚ
supportCoefficientAtCollar21 =
  Calibration.supportCountAsRational
  * (Calibration.epsilonAtCollar21 * Calibration.weightInflation)

supportCoefficientAtCollar21Exact :
  supportCoefficientAtCollar21 ≡ + 3 / 8
supportCoefficientAtCollar21Exact = ℚRing.solve []

supportCoefficientBelowHalf :
  supportCoefficientAtCollar21 ≤ + 1 / 2
supportCoefficientBelowHalf =
  subst
    (λ lower → lower ≤ (+ 1 / 2))
    (sym supportCoefficientAtCollar21Exact)
    Calibration.threeEighthsBelowHalf

supportBudgetAtWeight : ∀ weightValue →
  0ℚ ≤ weightValue →
  Calibration.supportCountAsRational
    * ((Calibration.epsilonAtCollar21 * Calibration.weightInflation)
      * weightValue)
  ≤ (+ 1 / 2) * weightValue
supportBudgetAtWeight weightValue weightNonnegative =
  let
    instance
      weightNN : NonNegative weightValue
      weightNN = ℚ.nonNegative weightNonnegative
    scaled = ℚP.*-monoʳ-≤-nonNeg weightValue supportCoefficientBelowHalf
  in
  subst
    (λ lower → lower ≤ (+ 1 / 2) * weightValue)
    (ℚRing.solve-∀ weightValue)
    scaled

asFiniteWeightedSupportCountHalf :
  ∀ hessian localParametrix →
  Calibration.PhysicalResidualEntryAtCollar21 hessian localParametrix →
  Support.FiniteWeightedSupportCountHalf
    Physical.PhysicalSU2Coordinate4
asFiniteWeightedSupportCountHalf hessian localParametrix entryEstimate = record
  { Support.FiniteWeightedSupportCountHalf.sites =
      Physical.physicalSU2Coordinates4
  ; Support.FiniteWeightedSupportCountHalf.kernel =
      Calibration.literalResidualKernel hessian localParametrix
  ; Support.FiniteWeightedSupportCountHalf.weight =
      Calibration.exponentialWeight entryEstimate
  ; Support.FiniteWeightedSupportCountHalf.epsilon =
      Calibration.epsilonAtCollar21
  ; Support.FiniteWeightedSupportCountHalf.weightInflation =
      Calibration.weightInflation
  ; Support.FiniteWeightedSupportCountHalf.weightNonnegative =
      Calibration.weightNonnegative entryEstimate
  ; Support.FiniteWeightedSupportCountHalf.entryWeightedBound =
      Calibration.weightedEntryBound entryEstimate
  ; Support.FiniteWeightedSupportCountHalf.supportCountBudget =
      λ left →
        subst
          (λ count →
            Sums.natAsRational count
              * ((Calibration.epsilonAtCollar21
                    * Calibration.weightInflation)
                * Calibration.exponentialWeight entryEstimate left)
            ≤ (+ 1 / 2)
              * Calibration.exponentialWeight entryEstimate left)
          (sym Calibration.supportCountExact)
          (supportBudgetAtWeight
            (Calibration.exponentialWeight entryEstimate left)
            (Calibration.weightNonnegative entryEstimate left))
  }

physicalResidualHalfRowContraction :
  ∀ hessian localParametrix →
  Calibration.PhysicalResidualEntryAtCollar21 hessian localParametrix →
  Row.FiniteWeightedRowContraction Physical.PhysicalSU2Coordinate4
physicalResidualHalfRowContraction hessian localParametrix entryEstimate =
  Support.asHalfWeightedRowContraction
    (asFiniteWeightedSupportCountHalf
      hessian localParametrix entryEstimate)

physicalResidualHalfRowBound :
  ∀ hessian localParametrix
    (entryEstimate : Calibration.PhysicalResidualEntryAtCollar21
      hessian localParametrix)
    left →
  Row.weightedRowSum
    Physical.physicalSU2Coordinates4
    (Calibration.literalResidualKernel hessian localParametrix)
    (Calibration.exponentialWeight entryEstimate)
    left
  ≤ (+ 1 / 2) * Calibration.exponentialWeight entryEstimate left
physicalResidualHalfRowBound hessian localParametrix entryEstimate =
  Support.weightedRowBelowHalf
    (asFiniteWeightedSupportCountHalf
      hessian localParametrix entryEstimate)

p33Collar21SupportPromotionLevel : ProofLevel
p33Collar21SupportPromotionLevel = machineChecked

p33PhysicalResidualHalfContractionLevel : ProofLevel
p33PhysicalResidualHalfContractionLevel = machineChecked
