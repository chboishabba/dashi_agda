module DASHI.Physics.YangMills.BalabanP33LiteralBondCellIncidenceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- DASHI CONTRIBUTION
--
-- The local P33 cell carrier is the literal side-four positive-bond carrier,
-- presented in axis-major order.  Its local charge is exactly one squared bond
-- coordinate.  Finite Cartesian Fubini therefore proves, rather than assumes,
--
--   sum_c q_c(v) = ||v||^2.
--
-- The five physical mechanisms may reuse this same exact incidence theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Rational using (ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (PhysicalBlockL; physicalBlockSites)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational)
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact using
  (sumCartesian)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using
  (side4)
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (sq)
import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact as Hodge

BondCell4 : Set
BondCell4 = Product Axis4 (PhysicalBlockL side4)

bondCells4 : List BondCell4
bondCells4 =
  cartesian (allCyclicIndices four) (physicalBlockSites side4)

bondCellValue : Hodge.RationalBondField4 → BondCell4 → ℚ
bondCellValue bondF (pair axis site) = bondF (pair site axis)

bondCellCharge : Hodge.RationalBondField4 → BondCell4 → ℚ
bondCellCharge bondF cell = sq (bondCellValue bondF cell)

bondCellChargeSumExact : ∀ bondF →
  sumRational bondCells4 (bondCellCharge bondF)
  ≡ Hodge.bondNormSq bondF
bondCellChargeSumExact bondF =
  trans
    (sumCartesian
      (allCyclicIndices four)
      (physicalBlockSites side4)
      (bondCellCharge bondF))
    refl

bondCellIncidenceBound : ∀ bondF →
  sumRational bondCells4 (bondCellCharge bondF)
  ≤ Hodge.bondNormSq bondF
bondCellIncidenceBound bondF
  rewrite bondCellChargeSumExact bondF =
  ℚP.≤-refl

bondCellCarrierLevel : ProofLevel
bondCellCarrierLevel = machineChecked

bondCellChargeFubiniLevel : ProofLevel
bondCellChargeFubiniLevel = machineChecked

fiveChannelIncidenceLevel : ProofLevel
fiveChannelIncidenceLevel = machineChecked
