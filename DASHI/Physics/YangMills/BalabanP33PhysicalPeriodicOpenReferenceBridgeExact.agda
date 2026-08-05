module DASHI.Physics.YangMills.BalabanP33PhysicalPeriodicOpenReferenceBridgeExact where

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
-- Connect the exact periodic four-dimensional Hodge identity to the actual P33
-- reference, whose axis fibres contain only the three open edges 0--1--2--3.
-- For every scalar bond component and derivative direction,
--
--   ||d_periodic f||^2
--     = E_open(f) + sum_transverse (f_0-f_3)^2.
--
-- Summing all four bond components and all three su(2) coordinates gives
--
--   H_gradient^periodic(h)
--     = H_diff^open(h) + H_boundary(h),
--
-- with H_boundary a literal finite sum of squares.  Together with periodic
-- Hodge this yields
--
--   H_curl^flat + H_div^flat
--     = H_diff^open + H_boundary.
--
-- Consequently the boundary term enters the exact physical Hessian remainder
-- with a positive sign and may be dropped safely in a lower bound.  The
-- corrected two analytic producers are therefore the Wilson-minus-flat-curl
-- and gauge-minus-flat-divergence estimates; no false equality between the
-- periodic and open reference energies is required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (Axis4; CyclicIndex; Product; pair; allCyclicIndices; four)
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact as Partition
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanPath4PhysicalComponentPoincareExact as Component
import DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact as Variance
import DASHI.Physics.YangMills.BalabanPath4ZeroMeanFibrePoincareExact as Fibre4
import DASHI.Physics.YangMills.BalabanPath4GlobalPoincareExact as Global
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2HodgeCoercivityExact as PhysicalHodge
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33OpenPeriodicBoundaryEnergyAuditExact as Boundary
import DASHI.Physics.YangMills.BalabanP33WilsonSharpBudgetCoercivityExact as Budget

------------------------------------------------------------------------
-- The nested periodic sum is the repository's literal global site sum.
------------------------------------------------------------------------

sumSitesMatchesCoordinateSum4 : ∀ term →
  Periodic.sumSites term ≡ Partition.coordinateSum4 term
sumSitesMatchesCoordinateSum4 term = refl

sumSitesMatchesGlobalSiteSum : ∀ term →
  Periodic.sumSites term ≡ Partition.globalSiteSum term
sumSitesMatchesGlobalSiteSum term =
  trans
    (sumSitesMatchesCoordinateSum4 term)
    (sym (Partition.globalSiteSumMatchesCoordinateSum4 term))

------------------------------------------------------------------------
-- One derivative direction: periodic energy = open energy + wrap squares.
------------------------------------------------------------------------

periodicFibreDifferenceSum :
  Sums.SiteField Path4.side4 → Axis4 →
  Block.Triple (CyclicIndex Path4.side4) → ℚ
periodicFibreDifferenceSum field axis transverse =
  Sums.sumRational (allCyclicIndices four)
    (λ coordinate →
      sq
        (field
          (Periodic.shiftForward axis
            (Block.insertAxis axis coordinate transverse))
        - field (Block.insertAxis axis coordinate transverse)))

periodicFibreDifferenceSumSplits :
  ∀ field axis transverse →
  periodicFibreDifferenceSum field axis transverse
  ≡ Variance.physicalFibreEdgeEnergy field axis transverse
    + Boundary.physicalFibreWrapEnergy field axis transverse
periodicFibreDifferenceSumSplits field Periodic.axis0
    (pair x1 (pair x2 x3))
  rewrite Fibre4.physicalFibre4EnergyExpansion
    field Periodic.axis0 (pair x1 (pair x2 x3)) =
  ℚRing.solve-∀
    (field (pair (pair Fibre4.index0 x1) (pair x2 x3)))
    (field (pair (pair Fibre4.index1 x1) (pair x2 x3)))
    (field (pair (pair Fibre4.index2 x1) (pair x2 x3)))
    (field (pair (pair Fibre4.index3 x1) (pair x2 x3)))
periodicFibreDifferenceSumSplits field Periodic.axis1
    (pair x0 (pair x2 x3))
  rewrite Fibre4.physicalFibre4EnergyExpansion
    field Periodic.axis1 (pair x0 (pair x2 x3)) =
  ℚRing.solve-∀
    (field (pair (pair x0 Fibre4.index0) (pair x2 x3)))
    (field (pair (pair x0 Fibre4.index1) (pair x2 x3)))
    (field (pair (pair x0 Fibre4.index2) (pair x2 x3)))
    (field (pair (pair x0 Fibre4.index3) (pair x2 x3)))
periodicFibreDifferenceSumSplits field Periodic.axis2
    (pair x0 (pair x1 x3))
  rewrite Fibre4.physicalFibre4EnergyExpansion
    field Periodic.axis2 (pair x0 (pair x1 x3)) =
  ℚRing.solve-∀
    (field (pair (pair x0 x1) (pair Fibre4.index0 x3)))
    (field (pair (pair x0 x1) (pair Fibre4.index1 x3)))
    (field (pair (pair x0 x1) (pair Fibre4.index2 x3)))
    (field (pair (pair x0 x1) (pair Fibre4.index3 x3)))
periodicFibreDifferenceSumSplits field Periodic.axis3
    (pair x0 (pair x1 x2))
  rewrite Fibre4.physicalFibre4EnergyExpansion
    field Periodic.axis3 (pair x0 (pair x1 x2)) =
  ℚRing.solve-∀
    (field (pair (pair x0 x1) (pair x2 Fibre4.index0)))
    (field (pair (pair x0 x1) (pair x2 Fibre4.index1)))
    (field (pair (pair x0 x1) (pair x2 Fibre4.index2)))
    (field (pair (pair x0 x1) (pair x2 Fibre4.index3)))

axisBoundaryWrapEnergy :
  Axis4 → Sums.SiteField Path4.side4 → ℚ
axisBoundaryWrapEnergy axis field =
  Sums.sumRational (Block.physicalTransverseCoordinates Path4.side4)
    (Boundary.physicalFibreWrapEnergy field axis)

axisPeriodicDifferenceEnergy :
  Axis4 → Sums.SiteField Path4.side4 → ℚ
axisPeriodicDifferenceEnergy axis field =
  Periodic.fieldNormSq (Periodic.forwardDifference axis field)

axisPeriodicDifferenceSplitsOpenAndBoundary : ∀ axis field →
  axisPeriodicDifferenceEnergy axis field
  ≡ Component.axisDirectionalEnergy axis field
    + axisBoundaryWrapEnergy axis field
axisPeriodicDifferenceSplitsOpenAndBoundary axis field =
  let
    siteTerm : Sums.SiteField Path4.side4
    siteTerm site =
      sq (field (Periodic.shiftForward axis site) - field site)

    partitioned :
      Partition.axisPartitionSum axis siteTerm
      ≡ Component.axisDirectionalEnergy axis field
        + axisBoundaryWrapEnergy axis field
    partitioned =
      trans
        (Sums.sumRationalCong
          (Block.physicalTransverseCoordinates Path4.side4)
          (λ transverse → periodicFibreDifferenceSum field axis transverse)
          (λ transverse →
            Variance.physicalFibreEdgeEnergy field axis transverse
            + Boundary.physicalFibreWrapEnergy field axis transverse)
          (periodicFibreDifferenceSumSplits field axis))
        (Fubini.sumRationalAdd
          (Block.physicalTransverseCoordinates Path4.side4)
          (Variance.physicalFibreEdgeEnergy field axis)
          (Boundary.physicalFibreWrapEnergy field axis))

    periodicAsGlobal :
      axisPeriodicDifferenceEnergy axis field
      ≡ Partition.globalSiteSum siteTerm
    periodicAsGlobal = sumSitesMatchesGlobalSiteSum siteTerm
  in
  trans periodicAsGlobal
    (trans
      (sym (Partition.axisPartitionSumMatchesGlobal axis siteTerm))
      partitioned)

------------------------------------------------------------------------
-- Scalar four-component and physical three-component boundary sums.
------------------------------------------------------------------------

scalarBoundaryWrapEnergy : Periodic.BondField4 → ℚ
scalarBoundaryWrapEnergy field =
  axisBoundaryWrapEnergy Periodic.axis0 (field Periodic.axis0)
  + axisBoundaryWrapEnergy Periodic.axis1 (field Periodic.axis0)
  + axisBoundaryWrapEnergy Periodic.axis2 (field Periodic.axis0)
  + axisBoundaryWrapEnergy Periodic.axis3 (field Periodic.axis0)
  + axisBoundaryWrapEnergy Periodic.axis0 (field Periodic.axis1)
  + axisBoundaryWrapEnergy Periodic.axis1 (field Periodic.axis1)
  + axisBoundaryWrapEnergy Periodic.axis2 (field Periodic.axis1)
  + axisBoundaryWrapEnergy Periodic.axis3 (field Periodic.axis1)
  + axisBoundaryWrapEnergy Periodic.axis0 (field Periodic.axis2)
  + axisBoundaryWrapEnergy Periodic.axis1 (field Periodic.axis2)
  + axisBoundaryWrapEnergy Periodic.axis2 (field Periodic.axis2)
  + axisBoundaryWrapEnergy Periodic.axis3 (field Periodic.axis2)
  + axisBoundaryWrapEnergy Periodic.axis0 (field Periodic.axis3)
  + axisBoundaryWrapEnergy Periodic.axis1 (field Periodic.axis3)
  + axisBoundaryWrapEnergy Periodic.axis2 (field Periodic.axis3)
  + axisBoundaryWrapEnergy Periodic.axis3 (field Periodic.axis3)

scalarOpenReferenceEnergy : Periodic.BondField4 → ℚ
scalarOpenReferenceEnergy field =
  Global.globalDirectionalEnergy (field Periodic.axis0)
  + Global.globalDirectionalEnergy (field Periodic.axis1)
  + Global.globalDirectionalEnergy (field Periodic.axis2)
  + Global.globalDirectionalEnergy (field Periodic.axis3)

scalarPeriodicGradientSplitsOpenAndBoundary : ∀ field →
  Periodic.periodicGradientEnergy field
  ≡ scalarOpenReferenceEnergy field + scalarBoundaryWrapEnergy field
scalarPeriodicGradientSplitsOpenAndBoundary field
  rewrite axisPeriodicDifferenceSplitsOpenAndBoundary
    Periodic.axis0 (field Periodic.axis0)
  | axisPeriodicDifferenceSplitsOpenAndBoundary
    Periodic.axis1 (field Periodic.axis0)
  | axisPeriodicDifferenceSplitsOpenAndBoundary
    Periodic.axis2 (field Periodic.axis0)
  | axisPeriodicDifferenceSplitsOpenAndBoundary
    Periodic.axis3 (field Periodic.axis0)
  | axisPeriodicDifferenceSplitsOpenAndBoundary
    Periodic.axis0 (field Periodic.axis1)
  | axisPeriodicDifferenceSplitsOpenAndBoundary
    Periodic.axis1 (field Periodic.axis1)
  | axisPeriodicDifferenceSplitsOpenAndBoundary
    Periodic.axis2 (field Periodic.axis1)
  | axisPeriodicDifferenceSplitsOpenAndBoundary
    Periodic.axis3 (field Periodic.axis1)
  | axisPeriodicDifferenceSplitsOpenAndBoundary
    Periodic.axis0 (field Periodic.axis2)
  | axisPeriodicDifferenceSplitsOpenAndBoundary
    Periodic.axis1 (field Periodic.axis2)
  | axisPeriodicDifferenceSplitsOpenAndBoundary
    Periodic.axis2 (field Periodic.axis2)
  | axisPeriodicDifferenceSplitsOpenAndBoundary
    Periodic.axis3 (field Periodic.axis2)
  | axisPeriodicDifferenceSplitsOpenAndBoundary
    Periodic.axis0 (field Periodic.axis3)
  | axisPeriodicDifferenceSplitsOpenAndBoundary
    Periodic.axis1 (field Periodic.axis3)
  | axisPeriodicDifferenceSplitsOpenAndBoundary
    Periodic.axis2 (field Periodic.axis3)
  | axisPeriodicDifferenceSplitsOpenAndBoundary
    Periodic.axis3 (field Periodic.axis3) =
  ℚRing.solve-∀

asPeriodicField :
  Physical.PhysicalSU2BondField4 → Periodic.PhysicalBondField4
asPeriodicField field coordinate axis site =
  field coordinate (pair site axis)

physicalBoundaryWrapEnergy : Physical.PhysicalSU2BondField4 → ℚ
physicalBoundaryWrapEnergy field =
  scalarBoundaryWrapEnergy (asPeriodicField field Physical.coordinateX)
  + scalarBoundaryWrapEnergy (asPeriodicField field Physical.coordinateY)
  + scalarBoundaryWrapEnergy (asPeriodicField field Physical.coordinateZ)

physicalPeriodicGradientSplitsOpenAndBoundary : ∀ field →
  Periodic.physicalPeriodicGradientEnergy (asPeriodicField field)
  ≡ PhysicalHodge.physicalReferenceDifferenceEnergy field
    + physicalBoundaryWrapEnergy field
physicalPeriodicGradientSplitsOpenAndBoundary field
  rewrite scalarPeriodicGradientSplitsOpenAndBoundary
    (asPeriodicField field Physical.coordinateX)
  | scalarPeriodicGradientSplitsOpenAndBoundary
    (asPeriodicField field Physical.coordinateY)
  | scalarPeriodicGradientSplitsOpenAndBoundary
    (asPeriodicField field Physical.coordinateZ) =
  ℚRing.solve-∀

------------------------------------------------------------------------
-- Boundary positivity and the corrected exact Hodge equation.
------------------------------------------------------------------------

axisBoundaryWrapEnergyNonnegative : ∀ axis field →
  0ℚ ≤ axisBoundaryWrapEnergy axis field
axisBoundaryWrapEnergyNonnegative axis field =
  Budget.Schur.sumNonnegative
    (Block.physicalTransverseCoordinates Path4.side4)
    (Boundary.physicalFibreWrapEnergy field axis)
    (λ transverse →
      Budget.FiniteL2.squareNonnegative
        (field (Block.insertAxis axis Boundary.index0 transverse)
        - field (Block.insertAxis axis Boundary.index3 transverse)))

scalarBoundaryWrapEnergyNonnegative : ∀ field →
  0ℚ ≤ scalarBoundaryWrapEnergy field
scalarBoundaryWrapEnergyNonnegative field =
  ℚP.+-mono-≤
    (ℚP.+-mono-≤
      (ℚP.+-mono-≤
        (ℚP.+-mono-≤
          (axisBoundaryWrapEnergyNonnegative Periodic.axis0 (field Periodic.axis0))
          (axisBoundaryWrapEnergyNonnegative Periodic.axis1 (field Periodic.axis0)))
        (ℚP.+-mono-≤
          (axisBoundaryWrapEnergyNonnegative Periodic.axis2 (field Periodic.axis0))
          (axisBoundaryWrapEnergyNonnegative Periodic.axis3 (field Periodic.axis0))))
      (ℚP.+-mono-≤
        (ℚP.+-mono-≤
          (axisBoundaryWrapEnergyNonnegative Periodic.axis0 (field Periodic.axis1))
          (axisBoundaryWrapEnergyNonnegative Periodic.axis1 (field Periodic.axis1)))
        (ℚP.+-mono-≤
          (axisBoundaryWrapEnergyNonnegative Periodic.axis2 (field Periodic.axis1))
          (axisBoundaryWrapEnergyNonnegative Periodic.axis3 (field Periodic.axis1)))))
    (ℚP.+-mono-≤
      (ℚP.+-mono-≤
        (ℚP.+-mono-≤
          (axisBoundaryWrapEnergyNonnegative Periodic.axis0 (field Periodic.axis2))
          (axisBoundaryWrapEnergyNonnegative Periodic.axis1 (field Periodic.axis2)))
        (ℚP.+-mono-≤
          (axisBoundaryWrapEnergyNonnegative Periodic.axis2 (field Periodic.axis2))
          (axisBoundaryWrapEnergyNonnegative Periodic.axis3 (field Periodic.axis2))))
      (ℚP.+-mono-≤
        (ℚP.+-mono-≤
          (axisBoundaryWrapEnergyNonnegative Periodic.axis0 (field Periodic.axis3))
          (axisBoundaryWrapEnergyNonnegative Periodic.axis1 (field Periodic.axis3)))
        (ℚP.+-mono-≤
          (axisBoundaryWrapEnergyNonnegative Periodic.axis2 (field Periodic.axis3))
          (axisBoundaryWrapEnergyNonnegative Periodic.axis3 (field Periodic.axis3)))))

physicalBoundaryWrapEnergyNonnegative : ∀ field →
  0ℚ ≤ physicalBoundaryWrapEnergy field
physicalBoundaryWrapEnergyNonnegative field =
  ℚP.+-mono-≤
    (ℚP.+-mono-≤
      (scalarBoundaryWrapEnergyNonnegative
        (asPeriodicField field Physical.coordinateX))
      (scalarBoundaryWrapEnergyNonnegative
        (asPeriodicField field Physical.coordinateY)))
    (scalarBoundaryWrapEnergyNonnegative
      (asPeriodicField field Physical.coordinateZ))

physicalFlatHodgeWithBoundary : ∀ field →
  Periodic.physicalPeriodicCurlEnergy (asPeriodicField field)
    + Periodic.physicalPeriodicDivergenceEnergy (asPeriodicField field)
  ≡ PhysicalHodge.physicalReferenceDifferenceEnergy field
    + physicalBoundaryWrapEnergy field
physicalFlatHodgeWithBoundary field =
  trans
    (sym (Periodic.physicalPeriodicHodgeIdentity (asPeriodicField field)))
    (physicalPeriodicGradientSplitsOpenAndBoundary field)

periodicOpenReferenceBridgeLevel : ProofLevel
periodicOpenReferenceBridgeLevel = machineChecked

physicalBoundaryWrapPositivityLevel : ProofLevel
physicalBoundaryWrapPositivityLevel = machineChecked

physicalFlatHodgeBoundaryIdentityLevel : ProofLevel
physicalFlatHodgeBoundaryIdentityLevel = machineChecked
