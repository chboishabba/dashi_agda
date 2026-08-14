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
periodicFibreDifferenceSum fieldValue axis transverse =
  Sums.sumRational axes4
    (λ coordinate →
      sq
        (fieldValue
          (Periodic.shiftForward axis
            (Block.insertAxis axis coordinate transverse))
        - fieldValue (Block.insertAxis axis coordinate transverse)))

periodicFibreDifferenceSumSplits :
  ∀ fieldValue axis transverse →
  periodicFibreDifferenceSum fieldValue axis transverse
  ≡ Variance.physicalFibreEdgeEnergy fieldValue axis transverse
    + Boundary.physicalFibreWrapEnergy fieldValue axis transverse
periodicFibreDifferenceSumSplits fieldValue Periodic.axis0
    (pair x1 (pair x2 x3)) =
  ℚRing.solve-∀
    (fieldValue (pair (pair Match.index0 x1) (pair x2 x3)))
    (fieldValue (pair (pair Match.index1 x1) (pair x2 x3)))
    (fieldValue (pair (pair Match.index2 x1) (pair x2 x3)))
    (fieldValue (pair (pair Match.index3 x1) (pair x2 x3)))
periodicFibreDifferenceSumSplits fieldValue Periodic.axis1
    (pair x0 (pair x2 x3)) =
  ℚRing.solve-∀
    (fieldValue (pair (pair x0 Match.index0) (pair x2 x3)))
    (fieldValue (pair (pair x0 Match.index1) (pair x2 x3)))
    (fieldValue (pair (pair x0 Match.index2) (pair x2 x3)))
    (fieldValue (pair (pair x0 Match.index3) (pair x2 x3)))
periodicFibreDifferenceSumSplits fieldValue Periodic.axis2
    (pair x0 (pair x1 x3)) =
  ℚRing.solve-∀
    (fieldValue (pair (pair x0 x1) (pair Match.index0 x3)))
    (fieldValue (pair (pair x0 x1) (pair Match.index1 x3)))
    (fieldValue (pair (pair x0 x1) (pair Match.index2 x3)))
    (fieldValue (pair (pair x0 x1) (pair Match.index3 x3)))
periodicFibreDifferenceSumSplits fieldValue Periodic.axis3
    (pair x0 (pair x1 x2)) =
  ℚRing.solve-∀
    (fieldValue (pair (pair x0 x1) (pair x2 Match.index0)))
    (fieldValue (pair (pair x0 x1) (pair x2 Match.index1)))
    (fieldValue (pair (pair x0 x1) (pair x2 Match.index2)))
    (fieldValue (pair (pair x0 x1) (pair x2 Match.index3)))

axisBoundaryWrapEnergy :
  Axis4 → Sums.SiteField Path4.side4 → ℚ
axisBoundaryWrapEnergy axis fieldValue =
  Sums.sumRational (Block.physicalTransverseCoordinates Path4.side4)
    (Boundary.physicalFibreWrapEnergy fieldValue axis)

axisPeriodicDifferenceEnergy :
  Axis4 → Sums.SiteField Path4.side4 → ℚ
axisPeriodicDifferenceEnergy axis fieldValue =
  Periodic.fieldNormSq (Periodic.forwardDifference axis fieldValue)

axisPeriodicDifferenceSplitsOpenAndBoundary : ∀ axis fieldValue →
  axisPeriodicDifferenceEnergy axis fieldValue
  ≡ Component.axisDirectionalEnergy axis fieldValue
    + axisBoundaryWrapEnergy axis fieldValue
axisPeriodicDifferenceSplitsOpenAndBoundary axis fieldValue =
  let
    siteTerm : Sums.SiteField Path4.side4
    siteTerm site =
      sq (fieldValue (Periodic.shiftForward axis site) - fieldValue site)

    asGlobal :
      axisPeriodicDifferenceEnergy axis fieldValue
      ≡ Partition.globalSiteSum siteTerm
    asGlobal = sumSitesMatchesGlobalSiteSum siteTerm

    asPartition :
      Partition.globalSiteSum siteTerm
      ≡ Partition.axisPartitionSum axis siteTerm
    asPartition = sym (Partition.axisPartitionSumMatchesGlobal axis siteTerm)

    splitFibres :
      Partition.axisPartitionSum axis siteTerm
      ≡ Component.axisDirectionalEnergy axis fieldValue
        + axisBoundaryWrapEnergy axis fieldValue
    splitFibres =
      trans
        (Sums.sumRationalCong
          (Block.physicalTransverseCoordinates Path4.side4)
          (periodicFibreDifferenceSum fieldValue axis)
          (λ transverse →
            Variance.physicalFibreEdgeEnergy fieldValue axis transverse
            + Boundary.physicalFibreWrapEnergy fieldValue axis transverse)
          (periodicFibreDifferenceSumSplits fieldValue axis))
        (Fubini.sumRationalAdd
          (Block.physicalTransverseCoordinates Path4.side4)
          (Variance.physicalFibreEdgeEnergy fieldValue axis)
          (Boundary.physicalFibreWrapEnergy fieldValue axis))
  in
  trans asGlobal (trans asPartition splitFibres)

scalarPeriodicGradientByAxes : Periodic.BondField4 → ℚ
scalarPeriodicGradientByAxes fieldValue =
  sumAxes (λ bondAxis →
    sumAxes (λ derivativeAxis →
      axisPeriodicDifferenceEnergy derivativeAxis (fieldValue bondAxis)))

scalarOpenReferenceByAxes : Periodic.BondField4 → ℚ
scalarOpenReferenceByAxes fieldValue =
  sumAxes (λ bondAxis →
    sumAxes (λ derivativeAxis →
      Component.axisDirectionalEnergy derivativeAxis (fieldValue bondAxis)))

scalarBoundaryWrapEnergy : Periodic.BondField4 → ℚ
scalarBoundaryWrapEnergy fieldValue =
  sumAxes (λ bondAxis →
    sumAxes (λ derivativeAxis →
      axisBoundaryWrapEnergy derivativeAxis (fieldValue bondAxis)))

periodicGradientMatchesDoubleAxisSum : ∀ fieldValue →
  Periodic.periodicGradientEnergy fieldValue
  ≡ scalarPeriodicGradientByAxes fieldValue
periodicGradientMatchesDoubleAxisSum fieldValue = refl

openReferenceMatchesDoubleAxisSum : ∀ fieldValue →
  ScalarHodge.bondReferenceDifferenceEnergy fieldValue
  ≡ scalarOpenReferenceByAxes fieldValue
openReferenceMatchesDoubleAxisSum fieldValue = refl

scalarPeriodicGradientSplitsOpenAndBoundary : ∀ fieldValue →
  Periodic.periodicGradientEnergy fieldValue
  ≡ ScalarHodge.bondReferenceDifferenceEnergy fieldValue
    + scalarBoundaryWrapEnergy fieldValue
scalarPeriodicGradientSplitsOpenAndBoundary fieldValue =
  trans
    (periodicGradientMatchesDoubleAxisSum fieldValue)
    (trans
      (Sums.sumRationalCong
        axes4
        (λ bondAxis →
          sumAxes (λ derivativeAxis →
            axisPeriodicDifferenceEnergy derivativeAxis (fieldValue bondAxis)))
        (λ bondAxis →
          sumAxes (λ derivativeAxis →
            Component.axisDirectionalEnergy derivativeAxis (fieldValue bondAxis)
            + axisBoundaryWrapEnergy derivativeAxis (fieldValue bondAxis)))
        (λ bondAxis →
          Sums.sumRationalCong
            axes4
            (λ derivativeAxis →
              axisPeriodicDifferenceEnergy derivativeAxis (fieldValue bondAxis))
            (λ derivativeAxis →
              Component.axisDirectionalEnergy derivativeAxis (fieldValue bondAxis)
              + axisBoundaryWrapEnergy derivativeAxis (fieldValue bondAxis))
            (λ derivativeAxis →
              axisPeriodicDifferenceSplitsOpenAndBoundary
                derivativeAxis (fieldValue bondAxis))))
      (trans
        (Sums.sumRationalCong
          axes4
          (λ bondAxis →
            sumAxes (λ derivativeAxis →
              Component.axisDirectionalEnergy derivativeAxis (fieldValue bondAxis)
              + axisBoundaryWrapEnergy derivativeAxis (fieldValue bondAxis)))
          (λ bondAxis →
            sumAxes (λ derivativeAxis →
              Component.axisDirectionalEnergy derivativeAxis (fieldValue bondAxis))
            + sumAxes (λ derivativeAxis →
              axisBoundaryWrapEnergy derivativeAxis (fieldValue bondAxis)))
          (λ bondAxis →
            sumAxesAdd
              (λ derivativeAxis →
                Component.axisDirectionalEnergy derivativeAxis (fieldValue bondAxis))
              (λ derivativeAxis →
                axisBoundaryWrapEnergy derivativeAxis (fieldValue bondAxis))))
        (trans
          (sumAxesAdd
            (λ bondAxis →
              sumAxes (λ derivativeAxis →
                Component.axisDirectionalEnergy derivativeAxis (fieldValue bondAxis)))
            (λ bondAxis →
              sumAxes (λ derivativeAxis →
                axisBoundaryWrapEnergy derivativeAxis (fieldValue bondAxis))))
          (cong
            (_+ scalarBoundaryWrapEnergy fieldValue)
            (sym (openReferenceMatchesDoubleAxisSum fieldValue))))))

asPeriodicField :
  Physical.PhysicalSU2BondField4 → Periodic.PhysicalBondField4
asPeriodicField fieldValue coordinate axis site =
  fieldValue coordinate (pair site axis)

physicalBoundaryWrapEnergy : Physical.PhysicalSU2BondField4 → ℚ
physicalBoundaryWrapEnergy fieldValue =
  scalarBoundaryWrapEnergy (asPeriodicField fieldValue Physical.coordinateX)
  + scalarBoundaryWrapEnergy (asPeriodicField fieldValue Physical.coordinateY)
  + scalarBoundaryWrapEnergy (asPeriodicField fieldValue Physical.coordinateZ)

physicalPeriodicGradientSplitsOpenAndBoundary : ∀ fieldValue →
  Periodic.physicalPeriodicGradientEnergy (asPeriodicField fieldValue)
  ≡ PhysicalHodge.physicalReferenceDifferenceEnergy fieldValue
    + physicalBoundaryWrapEnergy fieldValue
physicalPeriodicGradientSplitsOpenAndBoundary fieldValue
  rewrite scalarPeriodicGradientSplitsOpenAndBoundary
    (asPeriodicField fieldValue Physical.coordinateX)
  | scalarPeriodicGradientSplitsOpenAndBoundary
    (asPeriodicField fieldValue Physical.coordinateY)
  | scalarPeriodicGradientSplitsOpenAndBoundary
    (asPeriodicField fieldValue Physical.coordinateZ) =
  ℚRing.solve-∀
    (ScalarHodge.bondReferenceDifferenceEnergy
      (fieldValue Physical.coordinateX))
    (ScalarHodge.bondReferenceDifferenceEnergy
      (fieldValue Physical.coordinateY))
    (ScalarHodge.bondReferenceDifferenceEnergy
      (fieldValue Physical.coordinateZ))
    (scalarBoundaryWrapEnergy
      (asPeriodicField fieldValue Physical.coordinateX))
    (scalarBoundaryWrapEnergy
      (asPeriodicField fieldValue Physical.coordinateY))
    (scalarBoundaryWrapEnergy
      (asPeriodicField fieldValue Physical.coordinateZ))

axisBoundaryWrapEnergyNonnegative : ∀ axis fieldValue →
  0ℚ ≤ axisBoundaryWrapEnergy axis fieldValue
axisBoundaryWrapEnergyNonnegative axis fieldValue =
  Schur.sumNonnegative
    (Block.physicalTransverseCoordinates Path4.side4)
    (Boundary.physicalFibreWrapEnergy fieldValue axis)
    (λ transverse →
      FiniteL2.squareNonnegative
        (fieldValue (Block.insertAxis axis Match.index0 transverse)
        - fieldValue (Block.insertAxis axis Match.index3 transverse)))

scalarBoundaryWrapEnergyNonnegative : ∀ fieldValue →
  0ℚ ≤ scalarBoundaryWrapEnergy fieldValue
scalarBoundaryWrapEnergyNonnegative fieldValue =
  Schur.sumNonnegative axes4
    (λ bondAxis →
      sumAxes (λ derivativeAxis →
        axisBoundaryWrapEnergy derivativeAxis (fieldValue bondAxis)))
    (λ bondAxis →
      Schur.sumNonnegative axes4
        (λ derivativeAxis →
          axisBoundaryWrapEnergy derivativeAxis (fieldValue bondAxis))
        (λ derivativeAxis →
          axisBoundaryWrapEnergyNonnegative
            derivativeAxis (fieldValue bondAxis)))

physicalBoundaryWrapEnergyNonnegative : ∀ fieldValue →
  0ℚ ≤ physicalBoundaryWrapEnergy fieldValue
physicalBoundaryWrapEnergyNonnegative fieldValue =
  ℚP.+-mono-≤
    (ℚP.+-mono-≤
      (scalarBoundaryWrapEnergyNonnegative
        (asPeriodicField fieldValue Physical.coordinateX))
      (scalarBoundaryWrapEnergyNonnegative
        (asPeriodicField fieldValue Physical.coordinateY)))
    (scalarBoundaryWrapEnergyNonnegative
      (asPeriodicField fieldValue Physical.coordinateZ))

physicalFlatHodgeWithBoundary : ∀ fieldValue →
  Periodic.physicalPeriodicCurlEnergy (asPeriodicField fieldValue)
    + Periodic.physicalPeriodicDivergenceEnergy (asPeriodicField fieldValue)
  ≡ PhysicalHodge.physicalReferenceDifferenceEnergy fieldValue
    + physicalBoundaryWrapEnergy fieldValue
physicalFlatHodgeWithBoundary fieldValue =
  trans
    (sym (Periodic.physicalPeriodicHodgeIdentity (asPeriodicField fieldValue)))
    (physicalPeriodicGradientSplitsOpenAndBoundary fieldValue)

periodicOpenReferenceBridgeLevel : ProofLevel
periodicOpenReferenceBridgeLevel = machineChecked

physicalBoundaryWrapPositivityLevel : ProofLevel
physicalBoundaryWrapPositivityLevel = machineChecked

physicalFlatHodgeBoundaryIdentityLevel : ProofLevel
physicalFlatHodgeBoundaryIdentityLevel = machineChecked
