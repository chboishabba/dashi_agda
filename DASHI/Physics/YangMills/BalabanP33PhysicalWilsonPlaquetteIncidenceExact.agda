module DASHI.Physics.YangMills.BalabanP33PhysicalWilsonPlaquetteIncidenceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Replace the anonymous sixteen-atom budget bookkeeping by the literal
-- side-four physical plaquette incidence calculation.  For a plaquette
-- p=(x,mu,nu), let
--
--   q_p(h)=|h_mu(x)|^2+|h_nu(x+mu)|^2
--          +|h_mu(x+nu)|^2+|h_nu(x)|^2.
--
-- Every positive bond occurs in exactly six oriented axis-pair plaquettes, so
--
--   sum_p q_p(h)=6||h||^2.
--
-- The twelve ordered cross placements are charged by
--
--   1/2 (|X_i|^2+|X_j|^2),  i/=j.
--
-- Direct polynomial counting gives three copies of q_p per plaquette and hence
--
--   sum_p crossCharge_p(h)=18||h||^2.
--
-- Therefore the concrete local allocations
--
--   rho/36  for the ordered cross charge,
--   rho/144 for the diagonal charge
--
-- aggregate exactly to rho/2 and rho/24.  Any pointwise sixteen-atom defect
-- estimate with those two literal charges yields
--
--   -(13/24)rho ||h||^2 <= H_W(A;h)-H_W(1;h).
--
-- This is the physical W9 incidence theorem.  The remaining local analytic
-- task is now only the per-plaquette rational quaternion inequality; no global
-- multiplicity or norm-comparison premise remains.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (pair)
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact as Partition
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact as Variance
import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact as ScalarHodge
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalPeriodicOpenReferenceBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as WilsonPhysical
import DASHI.Physics.YangMills.BalabanP33WilsonSharpDuhamelBudgetExact as Sharp

------------------------------------------------------------------------
-- Literal link and plaquette charges.
------------------------------------------------------------------------

linkCharge :
  Physical.PhysicalSU2BondField4 →
  Periodic.Axis4 → Periodic.Site4 → ℚ
linkCharge field axis site =
  FiniteL2.square
    (field Physical.coordinateX (pair site axis))
  + FiniteL2.square
    (field Physical.coordinateY (pair site axis))
  + FiniteL2.square
    (field Physical.coordinateZ (pair site axis))

axisLinkCharge :
  Physical.PhysicalSU2BondField4 → Periodic.Axis4 → ℚ
axisLinkCharge field axis =
  Periodic.sumSites (linkCharge field axis)

plaquetteLink0 plaquetteLink1 plaquetteLink2 plaquetteLink3 :
  Physical.PhysicalSU2BondField4 →
  WilsonPhysical.Plaquette4 → ℚ
plaquetteLink0 field (pair site axes) =
  linkCharge field (WilsonPhysical.pairLeft axes) site
plaquetteLink1 field (pair site axes) =
  linkCharge field (WilsonPhysical.pairRight axes)
    (Periodic.shiftForward (WilsonPhysical.pairLeft axes) site)
plaquetteLink2 field (pair site axes) =
  linkCharge field (WilsonPhysical.pairLeft axes)
    (Periodic.shiftForward (WilsonPhysical.pairRight axes) site)
plaquetteLink3 field (pair site axes) =
  linkCharge field (WilsonPhysical.pairRight axes) site

plaquetteDiagonalCharge :
  Physical.PhysicalSU2BondField4 →
  WilsonPhysical.Plaquette4 → ℚ
plaquetteDiagonalCharge field plaquette =
  plaquetteLink0 field plaquette
  + plaquetteLink1 field plaquette
  + plaquetteLink2 field plaquette
  + plaquetteLink3 field plaquette

half : ℚ
half = + 1 / 2

plaquetteOrderedCrossCharge :
  Physical.PhysicalSU2BondField4 →
  WilsonPhysical.Plaquette4 → ℚ
plaquetteOrderedCrossCharge field plaquette =
  let
    a0 = plaquetteLink0 field plaquette
    a1 = plaquetteLink1 field plaquette
    a2 = plaquetteLink2 field plaquette
    a3 = plaquetteLink3 field plaquette
  in
  half * (a0 + a1) + half * (a0 + a2) + half * (a0 + a3)
  + half * (a1 + a0) + half * (a1 + a2) + half * (a1 + a3)
  + half * (a2 + a0) + half * (a2 + a1) + half * (a2 + a3)
  + half * (a3 + a0) + half * (a3 + a1) + half * (a3 + a2)

orderedCrossChargeIsThreeDiagonal : ∀ field plaquette →
  plaquetteOrderedCrossCharge field plaquette
  ≡ (+ 3 / 1) * plaquetteDiagonalCharge field plaquette
orderedCrossChargeIsThreeDiagonal field plaquette =
  ℚRing.solve-∀
    (plaquetteLink0 field plaquette)
    (plaquetteLink1 field plaquette)
    (plaquetteLink2 field plaquette)
    (plaquetteLink3 field plaquette)

------------------------------------------------------------------------
-- The physical periodic norm is the four-axis link-charge sum.
------------------------------------------------------------------------

axisLinkChargeMatchesPhysicalComponents : ∀ field axis →
  axisLinkCharge field axis
  ≡ Variance.globalNormSq
      (ScalarHodge.bondComponent (field Physical.coordinateX) axis)
    + Variance.globalNormSq
      (ScalarHodge.bondComponent (field Physical.coordinateY) axis)
    + Variance.globalNormSq
      (ScalarHodge.bondComponent (field Physical.coordinateZ) axis)
axisLinkChargeMatchesPhysicalComponents field axis =
  trans
    (Periodic.sumSitesAdd
      (λ site →
        FiniteL2.square
          (field Physical.coordinateX (pair site axis)))
      (λ site →
        FiniteL2.square
          (field Physical.coordinateY (pair site axis))
        + FiniteL2.square
          (field Physical.coordinateZ (pair site axis))))
    (trans
      (cong
        (Periodic.sumSites
          (λ site →
            FiniteL2.square
              (field Physical.coordinateX (pair site axis))) +_)
        (Periodic.sumSitesAdd
          (λ site →
            FiniteL2.square
              (field Physical.coordinateY (pair site axis)))
          (λ site →
            FiniteL2.square
              (field Physical.coordinateZ (pair site axis)))))
      (trans
        (cong
          (λ selected →
            selected
            + Periodic.sumSites
                (λ site →
                  FiniteL2.square
                    (field Physical.coordinateY (pair site axis)))
            + Periodic.sumSites
                (λ site →
                  FiniteL2.square
                    (field Physical.coordinateZ (pair site axis))))
          (Bridge.sumSitesMatchesGlobalSiteSum
            (λ site →
              FiniteL2.square
                (field Physical.coordinateX (pair site axis)))))
        (trans
          (cong
            (λ selected →
              Variance.globalNormSq
                (ScalarHodge.bondComponent
                  (field Physical.coordinateX) axis)
              + selected
              + Periodic.sumSites
                  (λ site →
                    FiniteL2.square
                      (field Physical.coordinateZ (pair site axis))))
            (Bridge.sumSitesMatchesGlobalSiteSum
              (λ site →
                FiniteL2.square
                  (field Physical.coordinateY (pair site axis)))))
          (cong
            (λ selected →
              Variance.globalNormSq
                (ScalarHodge.bondComponent
                  (field Physical.coordinateX) axis)
              + Variance.globalNormSq
                (ScalarHodge.bondComponent
                  (field Physical.coordinateY) axis)
              + selected)
            (Bridge.sumSitesMatchesGlobalSiteSum
              (λ site →
                FiniteL2.square
                  (field Physical.coordinateZ (pair site axis))))))))

physicalNormAsAxisLinkCharges : ∀ field →
  axisLinkCharge field Periodic.axis0
  + axisLinkCharge field Periodic.axis1
  + axisLinkCharge field Periodic.axis2
  + axisLinkCharge field Periodic.axis3
  ≡ Physical.physicalSU2BondNormSq field
physicalNormAsAxisLinkCharges field
  rewrite axisLinkChargeMatchesPhysicalComponents field Periodic.axis0
        | axisLinkChargeMatchesPhysicalComponents field Periodic.axis1
        | axisLinkChargeMatchesPhysicalComponents field Periodic.axis2
        | axisLinkChargeMatchesPhysicalComponents field Periodic.axis3 =
  ℚRing.solve-∀
    (Variance.globalNormSq
      (ScalarHodge.bondComponent (field Physical.coordinateX) Periodic.axis0))
    (Variance.globalNormSq
      (ScalarHodge.bondComponent (field Physical.coordinateX) Periodic.axis1))
    (Variance.globalNormSq
      (ScalarHodge.bondComponent (field Physical.coordinateX) Periodic.axis2))
    (Variance.globalNormSq
      (ScalarHodge.bondComponent (field Physical.coordinateX) Periodic.axis3))
    (Variance.globalNormSq
      (ScalarHodge.bondComponent (field Physical.coordinateY) Periodic.axis0))
    (Variance.globalNormSq
      (ScalarHodge.bondComponent (field Physical.coordinateY) Periodic.axis1))
    (Variance.globalNormSq
      (ScalarHodge.bondComponent (field Physical.coordinateY) Periodic.axis2))
    (Variance.globalNormSq
      (ScalarHodge.bondComponent (field Physical.coordinateY) Periodic.axis3))
    (Variance.globalNormSq
      (ScalarHodge.bondComponent (field Physical.coordinateZ) Periodic.axis0))
    (Variance.globalNormSq
      (ScalarHodge.bondComponent (field Physical.coordinateZ) Periodic.axis1))
    (Variance.globalNormSq
      (ScalarHodge.bondComponent (field Physical.coordinateZ) Periodic.axis2))
    (Variance.globalNormSq
      (ScalarHodge.bondComponent (field Physical.coordinateZ) Periodic.axis3))

------------------------------------------------------------------------
-- Every physical bond occurs in exactly six plaquette link slots.
------------------------------------------------------------------------

pairDiagonalChargeSum : ∀ field axes →
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ site →
      plaquetteDiagonalCharge field (pair site axes))
  ≡ (+ 2 / 1) * axisLinkCharge field (WilsonPhysical.pairLeft axes)
    + (+ 2 / 1) * axisLinkCharge field (WilsonPhysical.pairRight axes)
pairDiagonalChargeSum field axes =
  let
    left = WilsonPhysical.pairLeft axes
    right = WilsonPhysical.pairRight axes
    leftCharge = linkCharge field left
    rightCharge = linkCharge field right

    shiftedLeft :
      Periodic.sumSites (λ site → leftCharge (Periodic.shiftForward right site))
      ≡ Periodic.sumSites leftCharge
    shiftedLeft = Periodic.sumSitesForwardInvariant leftCharge right

    shiftedRight :
      Periodic.sumSites (λ site → rightCharge (Periodic.shiftForward left site))
      ≡ Periodic.sumSites rightCharge
    shiftedRight = Periodic.sumSitesForwardInvariant rightCharge left
  in
  trans
    (Bridge.sumSitesMatchesGlobalSiteSum
      (λ site → plaquetteDiagonalCharge field (pair site axes)))
    (trans
      (Partition.globalSiteSumMatchesCoordinateSum4
        (λ site → plaquetteDiagonalCharge field (pair site axes)))
      (trans
        (sym
          (Bridge.sumSitesMatchesCoordinateSum4
            (λ site → plaquetteDiagonalCharge field (pair site axes))))
        (trans
          (Periodic.sumSitesAdd
            leftCharge
            (λ site →
              rightCharge (Periodic.shiftForward left site)
              + leftCharge (Periodic.shiftForward right site)
              + rightCharge site))
          (trans
            (cong (Periodic.sumSites leftCharge +_)
              (trans
                (Periodic.sumSitesAdd
                  (λ site → rightCharge (Periodic.shiftForward left site))
                  (λ site →
                    leftCharge (Periodic.shiftForward right site)
                    + rightCharge site))
                (cong
                  (Periodic.sumSites
                    (λ site →
                      rightCharge (Periodic.shiftForward left site)) +_)
                  (Periodic.sumSitesAdd
                    (λ site → leftCharge (Periodic.shiftForward right site))
                    rightCharge))))
            (subst
              (λ shiftedRightValue →
                Periodic.sumSites leftCharge
                + (shiftedRightValue
                  + (Periodic.sumSites
                      (λ site → leftCharge (Periodic.shiftForward right site))
                    + Periodic.sumSites rightCharge))
                ≡ (+ 2 / 1) * Periodic.sumSites leftCharge
                  + (+ 2 / 1) * Periodic.sumSites rightCharge)
              shiftedRight
              (subst
                (λ shiftedLeftValue →
                  Periodic.sumSites leftCharge
                  + (Periodic.sumSites rightCharge
                    + (shiftedLeftValue + Periodic.sumSites rightCharge))
                  ≡ (+ 2 / 1) * Periodic.sumSites leftCharge
                    + (+ 2 / 1) * Periodic.sumSites rightCharge)
                shiftedLeft
                (ℚRing.solve-∀
                  (Periodic.sumSites leftCharge)
                  (Periodic.sumSites rightCharge)))))))))

sumPlaquetteDiagonalCharge :
  Physical.PhysicalSU2BondField4 → ℚ
sumPlaquetteDiagonalCharge field =
  Sums.sumRational WilsonPhysical.plaquettes4
    (plaquetteDiagonalCharge field)

sumPlaquetteDiagonalChargeIsSixNorm : ∀ field →
  sumPlaquetteDiagonalCharge field
  ≡ (+ 6 / 1) * Physical.physicalSU2BondNormSq field
sumPlaquetteDiagonalChargeIsSixNorm field =
  trans
    (Fubini.sumCartesian
      (Block.physicalBlockSites Path4.side4)
      WilsonPhysical.axisPairs6
      (plaquetteDiagonalCharge field))
    (trans
      (Fubini.sumSwap
        (Block.physicalBlockSites Path4.side4)
        WilsonPhysical.axisPairs6
        (λ site axes → plaquetteDiagonalCharge field (pair site axes)))
      (trans
        (Sums.sumRationalCong
          WilsonPhysical.axisPairs6
          (λ axes →
            Sums.sumRational (Block.physicalBlockSites Path4.side4)
              (λ site → plaquetteDiagonalCharge field (pair site axes)))
          (λ axes →
            (+ 2 / 1) * axisLinkCharge field (WilsonPhysical.pairLeft axes)
            + (+ 2 / 1) * axisLinkCharge field (WilsonPhysical.pairRight axes))
          (pairDiagonalChargeSum field))
        (trans
          (ℚRing.solve-∀
            (axisLinkCharge field Periodic.axis0)
            (axisLinkCharge field Periodic.axis1)
            (axisLinkCharge field Periodic.axis2)
            (axisLinkCharge field Periodic.axis3))
          (cong ((+ 6 / 1) *_)
            (physicalNormAsAxisLinkCharges field)))))

sumPlaquetteOrderedCrossCharge :
  Physical.PhysicalSU2BondField4 → ℚ
sumPlaquetteOrderedCrossCharge field =
  Sums.sumRational WilsonPhysical.plaquettes4
    (plaquetteOrderedCrossCharge field)

sumPlaquetteOrderedCrossChargeIsEighteenNorm : ∀ field →
  sumPlaquetteOrderedCrossCharge field
  ≡ (+ 18 / 1) * Physical.physicalSU2BondNormSq field
sumPlaquetteOrderedCrossChargeIsEighteenNorm field =
  trans
    (Sums.sumRationalCong
      WilsonPhysical.plaquettes4
      (plaquetteOrderedCrossCharge field)
      (λ plaquette →
        (+ 3 / 1) * plaquetteDiagonalCharge field plaquette)
      (orderedCrossChargeIsThreeDiagonal field))
    (trans
      (Sums.sumRationalScale
        (+ 3 / 1) WilsonPhysical.plaquettes4
        (plaquetteDiagonalCharge field))
      (trans
        (cong ((+ 3 / 1) *_)
          (sumPlaquetteDiagonalChargeIsSixNorm field))
        (ℚRing.solve-∀ (Physical.physicalSU2BondNormSq field))))

------------------------------------------------------------------------
-- Exact W9 sharp aggregation.
------------------------------------------------------------------------

localCrossCoefficient : ℚ
localCrossCoefficient = Sharp.rho * (+ 1 / 36)

localDiagonalCoefficient : ℚ
localDiagonalCoefficient = Sharp.rho * (+ 1 / 144)

plaquetteAllocatedCost :
  Physical.PhysicalSU2BondField4 → WilsonPhysical.Plaquette4 → ℚ
plaquetteAllocatedCost field plaquette =
  localCrossCoefficient * plaquetteOrderedCrossCharge field plaquette
  + localDiagonalCoefficient * plaquetteDiagonalCharge field plaquette

sumAllocatedCost : Physical.PhysicalSU2BondField4 → ℚ
sumAllocatedCost field =
  Sums.sumRational WilsonPhysical.plaquettes4
    (plaquetteAllocatedCost field)

sumAllocatedCostIsSharpBudget : ∀ field →
  sumAllocatedCost field
  ≡ Sharp.sharpSixteenAtomBudget
      * Physical.physicalSU2BondNormSq field
sumAllocatedCostIsSharpBudget field =
  trans
    (Fubini.sumRationalAdd
      WilsonPhysical.plaquettes4
      (λ plaquette →
        localCrossCoefficient * plaquetteOrderedCrossCharge field plaquette)
      (λ plaquette →
        localDiagonalCoefficient * plaquetteDiagonalCharge field plaquette))
    (trans
      (cong₂ _+_
        (Sums.sumRationalScale
          localCrossCoefficient WilsonPhysical.plaquettes4
          (plaquetteOrderedCrossCharge field))
        (Sums.sumRationalScale
          localDiagonalCoefficient WilsonPhysical.plaquettes4
          (plaquetteDiagonalCharge field)))
      (trans
        (cong₂ _+_
          (cong (localCrossCoefficient *_)
            (sumPlaquetteOrderedCrossChargeIsEighteenNorm field))
          (cong (localDiagonalCoefficient *_)
            (sumPlaquetteDiagonalChargeIsSixNorm field)))
        (ℚRing.solve-∀
          Sharp.rho (Physical.physicalSU2BondNormSq field))))

plaquetteWilsonDefect :
  WilsonPhysical.RationalSU2Background4 →
  Physical.PhysicalSU2BondField4 →
  WilsonPhysical.Plaquette4 → ℚ
plaquetteWilsonDefect background field plaquette =
  WilsonPhysical.plaquetteWilsonSecondVariation background field plaquette
  - WilsonPhysical.plaquetteWilsonSecondVariation
      WilsonPhysical.identityBackground field plaquette

sumPlaquetteWilsonDefect :
  WilsonPhysical.RationalSU2Background4 →
  Physical.PhysicalSU2BondField4 → ℚ
sumPlaquetteWilsonDefect background field =
  Sums.sumRational WilsonPhysical.plaquettes4
    (plaquetteWilsonDefect background field)

sumPlaquetteWilsonDefectIsPhysicalDefect : ∀ background field →
  sumPlaquetteWilsonDefect background field
  ≡ WilsonPhysical.physicalWilsonDefect background field
sumPlaquetteWilsonDefectIsPhysicalDefect background field =
  trans
    (Sums.sumRationalCong
      WilsonPhysical.plaquettes4
      (plaquetteWilsonDefect background field)
      (λ plaquette →
        WilsonPhysical.plaquetteWilsonSecondVariation background field plaquette
        + - WilsonPhysical.plaquetteWilsonSecondVariation
            WilsonPhysical.identityBackground field plaquette)
      (λ plaquette → ℚRing.solve []))
    (trans
      (Fubini.sumRationalAdd
        WilsonPhysical.plaquettes4
        (WilsonPhysical.plaquetteWilsonSecondVariation background field)
        (λ plaquette →
          - WilsonPhysical.plaquetteWilsonSecondVariation
              WilsonPhysical.identityBackground field plaquette))
      (trans
        (cong
          (WilsonPhysical.physicalWilsonSecondVariation background field +_)
          (Sums.sumRationalNegate
            WilsonPhysical.plaquettes4
            (WilsonPhysical.plaquetteWilsonSecondVariation
              WilsonPhysical.identityBackground field)))
        (ℚRing.solve-∀
          (WilsonPhysical.physicalWilsonSecondVariation background field)
          (WilsonPhysical.physicalWilsonSecondVariation
            WilsonPhysical.identityBackground field))))

sharpPhysicalWilsonDefectFromPointwisePlaquettes :
  ∀ background field →
  (∀ plaquette →
    - plaquetteAllocatedCost field plaquette
    ≤ plaquetteWilsonDefect background field plaquette) →
  - (Sharp.sharpSixteenAtomBudget
      * Physical.physicalSU2BondNormSq field)
  ≤ WilsonPhysical.physicalWilsonDefect background field
sharpPhysicalWilsonDefectFromPointwisePlaquettes
    background field pointwise =
  let
    summed :
      Sums.sumRational WilsonPhysical.plaquettes4
        (λ plaquette → - plaquetteAllocatedCost field plaquette)
      ≤ sumPlaquetteWilsonDefect background field
    summed =
      Schur.sumPointwiseBelow
        WilsonPhysical.plaquettes4
        (λ plaquette → - plaquetteAllocatedCost field plaquette)
        (plaquetteWilsonDefect background field)
        pointwise

    negatedCost :
      Sums.sumRational WilsonPhysical.plaquettes4
        (λ plaquette → - plaquetteAllocatedCost field plaquette)
      ≡ - sumAllocatedCost field
    negatedCost =
      Sums.sumRationalNegate
        WilsonPhysical.plaquettes4 (plaquetteAllocatedCost field)
  in
  subst
    (λ lower →
      lower ≤ WilsonPhysical.physicalWilsonDefect background field)
    (trans
      negatedCost
      (cong -_ (sumAllocatedCostIsSharpBudget field)))
    (subst
      (λ upper →
        Sums.sumRational WilsonPhysical.plaquettes4
          (λ plaquette → - plaquetteAllocatedCost field plaquette)
        ≤ upper)
      (sumPlaquetteWilsonDefectIsPhysicalDefect background field)
      summed)

physicalPlaquetteDiagonalIncidenceLevel : ProofLevel
physicalPlaquetteDiagonalIncidenceLevel = machineChecked

physicalPlaquetteCrossIncidenceLevel : ProofLevel
physicalPlaquetteCrossIncidenceLevel = machineChecked

physicalWilsonSharpW9AggregationLevel : ProofLevel
physicalWilsonSharpW9AggregationLevel = machineChecked

physicalWilsonLocalAtomEstimateLevel : ProofLevel
physicalWilsonLocalAtomEstimateLevel = conditional
