module DASHI.Physics.YangMills.BalabanP33OpenPeriodicBoundaryEnergyAuditExact where

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
-- Audit the boundary convention of the current side-four reference energy.
-- The carrier is cyclic, but `physicalFibreEdgeEnergy` deliberately sums only
-- the three open path edges
--
--   0--1, 1--2, 2--3.
--
-- A periodic Wilson/Hodge comparison also contains the wrap edge 3--0.  This
-- module proves exactly
--
--   E_cycle = E_open + (f_0-f_3)^2
--
-- on every physical fibre and exhibits the concrete witness
--
--   f=(0,0,0,1):  E_open=1, E_cycle=2.
--
-- Therefore a periodic flat curl-plus-divergence identity cannot be identified
-- with the present open reference difference energy without a boundary/collar
-- term or an explicit boundary condition killing the wrap square.  This is a
-- kernel-visible mathematical obstruction, not a documentation caveat.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (Axis4; CyclicIndex)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (Triple; SiteField; insertAxis)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanPath4PhysicalFibreMatchExact using
  (index0; index1; index2; index3)
open import DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact using
  (physicalFibreEdgeEnergy)

------------------------------------------------------------------------
-- Exact one-fibre arithmetic.
------------------------------------------------------------------------

openPathEnergy4 : ℚ → ℚ → ℚ → ℚ → ℚ
openPathEnergy4 f0 f1 f2 f3 =
  sq (f1 - f0)
  + (sq (f2 - f1)
  + (sq (f3 - f2) + 0ℚ))

wrapEdgeEnergy4 : ℚ → ℚ → ℚ
wrapEdgeEnergy4 f0 f3 = sq (f0 - f3)

periodicCycleEnergy4 : ℚ → ℚ → ℚ → ℚ → ℚ
periodicCycleEnergy4 f0 f1 f2 f3 =
  openPathEnergy4 f0 f1 f2 f3 + wrapEdgeEnergy4 f0 f3

periodicCycleSplitsOpenAndWrap : ∀ f0 f1 f2 f3 →
  periodicCycleEnergy4 f0 f1 f2 f3
  ≡ openPathEnergy4 f0 f1 f2 f3 + wrapEdgeEnergy4 f0 f3
periodicCycleSplitsOpenAndWrap f0 f1 f2 f3 = refl

unitBoundaryOpenEnergy :
  openPathEnergy4 0ℚ 0ℚ 0ℚ (+ 1 / 1) ≡ + 1 / 1
unitBoundaryOpenEnergy = ℚRing.solve []

unitBoundaryWrapEnergy :
  wrapEdgeEnergy4 0ℚ (+ 1 / 1) ≡ + 1 / 1
unitBoundaryWrapEnergy = ℚRing.solve []

unitBoundaryPeriodicEnergy :
  periodicCycleEnergy4 0ℚ 0ℚ 0ℚ (+ 1 / 1) ≡ + 2 / 1
unitBoundaryPeriodicEnergy = ℚRing.solve []

unitBoundaryPeriodicMinusOpen :
  periodicCycleEnergy4 0ℚ 0ℚ 0ℚ (+ 1 / 1)
    - openPathEnergy4 0ℚ 0ℚ 0ℚ (+ 1 / 1)
  ≡ + 1 / 1
unitBoundaryPeriodicMinusOpen = ℚRing.solve []

------------------------------------------------------------------------
-- Literal physical fibre specialization.
------------------------------------------------------------------------

physicalFibreWrapEnergy :
  SiteField side4 → Axis4 → Triple (CyclicIndex side4) → ℚ
physicalFibreWrapEnergy field axis transverse =
  sq
    (field (insertAxis axis index0 transverse)
    - field (insertAxis axis index3 transverse))

physicalFibrePeriodicEdgeEnergy :
  SiteField side4 → Axis4 → Triple (CyclicIndex side4) → ℚ
physicalFibrePeriodicEdgeEnergy field axis transverse =
  physicalFibreEdgeEnergy field axis transverse
  + physicalFibreWrapEnergy field axis transverse

physicalOpenFibreIsPathEnergy : ∀ field axis transverse →
  physicalFibreEdgeEnergy field axis transverse
  ≡ openPathEnergy4
      (field (insertAxis axis index0 transverse))
      (field (insertAxis axis index1 transverse))
      (field (insertAxis axis index2 transverse))
      (field (insertAxis axis index3 transverse))
physicalOpenFibreIsPathEnergy field axis transverse = refl

physicalPeriodicFibreIsCycleEnergy : ∀ field axis transverse →
  physicalFibrePeriodicEdgeEnergy field axis transverse
  ≡ periodicCycleEnergy4
      (field (insertAxis axis index0 transverse))
      (field (insertAxis axis index1 transverse))
      (field (insertAxis axis index2 transverse))
      (field (insertAxis axis index3 transverse))
physicalPeriodicFibreIsCycleEnergy field axis transverse =
  trans
    (cong
      (_+ physicalFibreWrapEnergy field axis transverse)
      (physicalOpenFibreIsPathEnergy field axis transverse))
    refl

physicalPeriodicFibreSplitsOpenAndWrap : ∀ field axis transverse →
  physicalFibrePeriodicEdgeEnergy field axis transverse
  ≡ physicalFibreEdgeEnergy field axis transverse
    + physicalFibreWrapEnergy field axis transverse
physicalPeriodicFibreSplitsOpenAndWrap field axis transverse = refl

openPathBoundaryConventionLevel : ProofLevel
openPathBoundaryConventionLevel = machineChecked

periodicWrapDefectWitnessLevel : ProofLevel
periodicWrapDefectWitnessLevel = machineChecked

physicalFibreBoundaryDefectLevel : ProofLevel
physicalFibreBoundaryDefectLevel = machineChecked
