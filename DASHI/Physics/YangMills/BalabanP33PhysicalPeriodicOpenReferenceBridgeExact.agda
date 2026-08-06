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
-- reference, whose side-four fibres contain the three open edges
-- 0--1, 1--2 and 2--3.  For every scalar bond component and derivative axis,
--
--   ||d_periodic f||^2
--     = E_open(f) + sum_transverse (f_0-f_3)^2.
--
-- The proof uses the repository's literal axis partition rather than an
-- anonymous cardinality factor.  Summing the four derivative axes, four bond
-- components and three su(2) coordinates gives
--
--   H_gradient^periodic(h)
--     = H_diff^open(h) + H_boundary(h),
--
-- where H_boundary is an explicit finite double-axis sum of fibre wrap
-- squares.  It is proved nonnegative term by term.  Combining with the exact
-- periodic Hodge identity yields
--
--   H_curl^flat + H_div^flat
--     = H_diff^open + H_boundary.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (Axis4; CyclicIndex; pair; allCyclicIndices; four)
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact as Partition
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanPath4PhysicalFibreMatchExact as Match
import DASHI.Physics.YangMills.BalabanPath4PhysicalComponentPoincareExact as Component
import DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact as Variance
import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact as ScalarHodge
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2HodgeCoercivityExact as PhysicalHodge
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33OpenPeriodicBoundaryEnergyAuditExact as Boundary

axes4 : List Axis4
axes4 = allCyclicIndices four

sumAxes : (Axis4 → ℚ) → ℚ
sumAxes term = Sums.sumRational axes4 term

sumAxesAdd : ∀ left right →
  sumAxes (λ axis → left axis + right axis)
  ≡ sumAxes left + sumAxes right
sumAxesAdd left right = Fubini.sumRationalAdd axes4 left right

sumSitesMatchesCoordinateSum4 : ∀ term →
  Periodic.sumSites term ≡ Partition.coordinateSum4 term
sumSitesMatchesCoordinateSum4 term = refl

sumSitesMatchesGlobalSiteSum : ∀ term →
  Periodic.sumSites term ≡ Partition.globalSiteSum term
sumSitesMatchesGlobalSiteSum term =
  trans
    (sumSitesMatchesCoordinateSum4 term)
    (sym (Partition.globalSiteSumMatchesCoordinateSum4 term))

periodicFibreDifferenceSum :
  Sums.SiteField Path4.side4 → Axis4 →
  Block.Triple (CyclicIndex Path4.side4) → ℚ
periodicFibreDifferenceSum field axis transverse =
  Sums.sumRational axes4
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
    (pair x1 (pair x2 x3)) =
  ℚRing.solve-∀
    (field (pair (pair Match.index0 x1) (pair x2 x3)))
    (field (pair (pair Match.index1 x1) (pair x2 x3)))
    (field (pair (pair Match.index2 x1) (pair x2 x3)))
    (field (pair (pair Match.index3 x1) (pair x2 x3)))
periodicFibreDifferenceSumSplits field Periodic.axis1
    (pair x0 (pair x2 x3)) =
  ℚRing.solve-∀
    (field (pair (pair x0 Match.index0) (pair x2 x3)))
    (field (pair (pair x0 Match.index1) (pair x2 x3)))
    (field (pair (pair x0 Match.index2) (pair x2 x3)))
    (field (pair (pair x0 Match.index3) (pair x2 x3)))
periodicFibreDifferenceSumSplits field Periodic.axis2
    (pair x0 (pair x1 x3)) =
  ℚRing.solve-∀
    (field (pair (pair x0 x1) (pair Match.index0 x3)))
    (field (pair (pair x0 x1) (pair Match.index1 x3)))
    (field (pair (pair x0 x1) (pair Match.index2 x3)))
    (field (pair (pair x0 x1) (pair Match.index3 x3)))
periodicFibreDifferenceSumSplits field Periodic.axis3
    (pair x0 (pair x1 x2)) =
  ℚRing.solve-∀
    (field (pair (pair x0 x1) (pair x2 Match.index0)))
    (field (pair (pair x0 x1) (pair x2 Match.index1)))
    (field (pair (pair x0 x1) (pair x2 Match.index2)))
    (field (pair (pair x0 x1) (pair x2 Match.index3)))

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

    asGlobal :
      axisPeriodicDifferenceEnergy axis field
      ≡ Partition.globalSiteSum siteTerm
    asGlobal = sumSitesMatchesGlobalSiteSum siteTerm

    asPartition :
      Partition.globalSiteSum siteTerm
      ≡ Partition.axisPartitionSum axis siteTerm
    asPartition = sym (Partition.axisPartitionSumMatchesGlobal axis siteTerm)

    splitFibres :
      Partition.axisPartitionSum axis siteTerm
      ≡ Component.axisDirectionalEnergy axis field
        + axisBoundaryWrapEnergy axis field
    splitFibres =
      trans
        (Sums.sumRationalCong
          (Block.physicalTransverseCoordinates Path4.side4)
          (periodicFibreDifferenceSum field axis)
          (λ transverse →
            Variance.physicalFibreEdgeEnergy field axis transverse
            + Boundary.physicalFibreWrapEnergy field axis transverse)
          (periodicFibreDifferenceSumSplits field axis))
        (Fubini.sumRationalAdd
          (Block.physicalTransverseCoordinates Path4.side4)
          (Variance.physicalFibreEdgeEnergy field axis)
          (Boundary.physicalFibreWrapEnergy field axis))
  in
  trans asGlobal (trans asPartition splitFibres)

scalarPeriodicGradientByAxes : Periodic.BondField4 → ℚ
scalarPeriodicGradientByAxes field =
  sumAxes (λ bondAxis →
    sumAxes (λ derivativeAxis →
      axisPeriodicDifferenceEnergy derivativeAxis (field bondAxis)))

scalarOpenReferenceByAxes : Periodic.BondField4 → ℚ
scalarOpenReferenceByAxes field =
  sumAxes (λ bondAxis →
    sumAxes (λ derivativeAxis →
      Component.axisDirectionalEnergy derivativeAxis (field bondAxis)))

scalarBoundaryWrapEnergy : Periodic.BondField4 → ℚ
scalarBoundaryWrapEnergy field =
  sumAxes (λ bondAxis →
    sumAxes (λ derivativeAxis →
      axisBoundaryWrapEnergy derivativeAxis (field bondAxis)))

periodicGradientMatchesDoubleAxisSum : ∀ field →
  Periodic.periodicGradientEnergy field
  ≡ scalarPeriodicGradientByAxes field
periodicGradientMatchesDoubleAxisSum field = refl

openReferenceMatchesDoubleAxisSum : ∀ field →
  ScalarHodge.bondReferenceDifferenceEnergy field
  ≡ scalarOpenReferenceByAxes field
openReferenceMatchesDoubleAxisSum field = refl

scalarPeriodicGradientSplitsOpenAndBoundary : ∀ field →
  Periodic.periodicGradientEnergy field
  ≡ ScalarHodge.bondReferenceDifferenceEnergy field
    + scalarBoundaryWrapEnergy field
scalarPeriodicGradientSplitsOpenAndBoundary field =
  trans
    (periodicGradientMatchesDoubleAxisSum field)
    (trans
      (Sums.sumRationalCong
        axes4
        (λ bondAxis →
          sumAxes (λ derivativeAxis →
            axisPeriodicDifferenceEnergy derivativeAxis (field bondAxis)))
        (λ bondAxis →
          sumAxes (λ derivativeAxis →
            Component.axisDirectionalEnergy derivativeAxis (field bondAxis)
            + axisBoundaryWrapEnergy derivativeAxis (field bondAxis)))
        (λ bondAxis →
          Sums.sumRationalCong
            axes4
            (λ derivativeAxis →
              axisPeriodicDifferenceEnergy derivativeAxis (field bondAxis))
            (λ derivativeAxis →
              Component.axisDirectionalEnergy derivativeAxis (field bondAxis)
              + axisBoundaryWrapEnergy derivativeAxis (field bondAxis))
            (λ derivativeAxis →
              axisPeriodicDifferenceSplitsOpenAndBoundary
                derivativeAxis (field bondAxis))))
      (trans
        (Sums.sumRationalCong
          axes4
          (λ bondAxis →
            sumAxes (λ derivativeAxis →
              Component.axisDirectionalEnergy derivativeAxis (field bondAxis)
              + axisBoundaryWrapEnergy derivativeAxis (field bondAxis)))
          (λ bondAxis →
            sumAxes (λ derivativeAxis →
              Component.axisDirectionalEnergy derivativeAxis (field bondAxis))
            + sumAxes (λ derivativeAxis →
              axisBoundaryWrapEnergy derivativeAxis (field bondAxis)))
          (λ bondAxis →
            sumAxesAdd
              (λ derivativeAxis →
                Component.axisDirectionalEnergy derivativeAxis (field bondAxis))
              (λ derivativeAxis →
                axisBoundaryWrapEnergy derivativeAxis (field bondAxis))))
        (trans
          (sumAxesAdd
            (λ bondAxis →
              sumAxes (λ derivativeAxis →
                Component.axisDirectionalEnergy derivativeAxis (field bondAxis)))
            (λ bondAxis →
              sumAxes (λ derivativeAxis →
                axisBoundaryWrapEnergy derivativeAxis (field bondAxis))))
          (cong
            (_+ scalarBoundaryWrapEnergy field)
            (sym (openReferenceMatchesDoubleAxisSum field))))))

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
    (ScalarHodge.bondReferenceDifferenceEnergy
      (field Physical.coordinateX))
    (ScalarHodge.bondReferenceDifferenceEnergy
      (field Physical.coordinateY))
    (ScalarHodge.bondReferenceDifferenceEnergy
      (field Physical.coordinateZ))
    (scalarBoundaryWrapEnergy
      (asPeriodicField field Physical.coordinateX))
    (scalarBoundaryWrapEnergy
      (asPeriodicField field Physical.coordinateY))
    (scalarBoundaryWrapEnergy
      (asPeriodicField field Physical.coordinateZ))

axisBoundaryWrapEnergyNonnegative : ∀ axis field →
  0ℚ ≤ axisBoundaryWrapEnergy axis field
axisBoundaryWrapEnergyNonnegative axis field =
  Schur.sumNonnegative
    (Block.physicalTransverseCoordinates Path4.side4)
    (Boundary.physicalFibreWrapEnergy field axis)
    (λ transverse →
      FiniteL2.squareNonnegative
        (field (Block.insertAxis axis Match.index0 transverse)
        - field (Block.insertAxis axis Match.index3 transverse)))

scalarBoundaryWrapEnergyNonnegative : ∀ field →
  0ℚ ≤ scalarBoundaryWrapEnergy field
scalarBoundaryWrapEnergyNonnegative field =
  Schur.sumNonnegative axes4
    (λ bondAxis →
      sumAxes (λ derivativeAxis →
        axisBoundaryWrapEnergy derivativeAxis (field bondAxis)))
    (λ bondAxis →
      Schur.sumNonnegative axes4
        (λ derivativeAxis →
          axisBoundaryWrapEnergy derivativeAxis (field bondAxis))
        (λ derivativeAxis →
          axisBoundaryWrapEnergyNonnegative
            derivativeAxis (field bondAxis)))

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
