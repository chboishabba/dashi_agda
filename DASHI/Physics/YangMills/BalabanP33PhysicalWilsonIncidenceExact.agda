module DASHI.Physics.YangMills.BalabanP33PhysicalWilsonIncidenceExact where

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
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- DASHI CONTRIBUTION
--
-- Construct the actual plaquette-local charges used by the signed Wilson
-- estimate on the literal side-four torus.  For the four ordered boundary
-- slots of a plaquette, q_p is the sum of the four insertion norm squares.
-- For each of the twelve ordered distinct slot pairs, C_p contributes one half
-- of the two endpoint charges.  Thus each of the four slots occurs six times
-- in C_p and
--
--   C_p = 3 q_p.
--
-- Finite periodic reindexing then proves, rather than assumes,
--
--   sum_p q_p(h) = 6 ||h||^2,
--   sum_p C_p(h) = 18 ||h||^2.
--
-- The factors six and eighteen come from the six axis pairs and the literal
-- four-link/twelve-ordered-pair enumeration, not from anonymous incidence
-- constants.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as Gauge
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeGlobalDefectExact as Global
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33WilsonPlaquetteSecondVariationPlacementsExact as Placement

linkInsertionCharge :
  Coordinates.PhysicalSU2BondField4 →
  Periodic.Axis4 → Periodic.Site4 → ℚ
linkInsertionCharge fieldValue axis site =
  Norm.normSq (Gauge.insertionQuaternion fieldValue axis site)

plaquetteSlotCharge :
  Coordinates.PhysicalSU2BondField4 →
  Periodic.Axis4 → Periodic.Axis4 → Periodic.Site4 →
  Placement.PlaquetteLinkSlot4 → ℚ
plaquetteSlotCharge fieldValue left right site Placement.slot0 =
  linkInsertionCharge fieldValue left site
plaquetteSlotCharge fieldValue left right site Placement.slot1 =
  linkInsertionCharge fieldValue right (Periodic.shiftForward left site)
plaquetteSlotCharge fieldValue left right site Placement.slot2 =
  linkInsertionCharge fieldValue left (Periodic.shiftForward right site)
plaquetteSlotCharge fieldValue left right site Placement.slot3 =
  linkInsertionCharge fieldValue right site

plaquetteDiagonalCharge :
  Coordinates.PhysicalSU2BondField4 →
  Periodic.Axis4 → Periodic.Axis4 → Periodic.Site4 → ℚ
plaquetteDiagonalCharge fieldValue left right site =
  Sums.sumRational Placement.plaquetteLinkSlots4
    (plaquetteSlotCharge fieldValue left right site)

orderedCrossCharge :
  Coordinates.PhysicalSU2BondField4 →
  Periodic.Axis4 → Periodic.Axis4 → Periodic.Site4 →
  Placement.OrderedDistinctSlotPair4 → ℚ
orderedCrossCharge fieldValue left right site pair =
  (+ 1 / 2)
    * (plaquetteSlotCharge fieldValue left right site
        (Placement.orderedPairFirst pair)
      + plaquetteSlotCharge fieldValue left right site
        (Placement.orderedPairSecond pair))

plaquetteCrossCharge :
  Coordinates.PhysicalSU2BondField4 →
  Periodic.Axis4 → Periodic.Axis4 → Periodic.Site4 → ℚ
plaquetteCrossCharge fieldValue left right site =
  Sums.sumRational Placement.orderedDistinctSlotPairs4
    (orderedCrossCharge fieldValue left right site)

plaquetteDiagonalChargeExpanded : ∀ fieldValue left right site →
  plaquetteDiagonalCharge fieldValue left right site
  ≡ linkInsertionCharge fieldValue left site
    + linkInsertionCharge fieldValue right (Periodic.shiftForward left site)
    + linkInsertionCharge fieldValue left (Periodic.shiftForward right site)
    + linkInsertionCharge fieldValue right site
plaquetteDiagonalChargeExpanded fieldValue left right site =
  ℚRing.solve-∀
    (linkInsertionCharge fieldValue left site)
    (linkInsertionCharge fieldValue right (Periodic.shiftForward left site))
    (linkInsertionCharge fieldValue left (Periodic.shiftForward right site))
    (linkInsertionCharge fieldValue right site)

plaquetteCrossChargeIsThreeDiagonal : ∀ fieldValue left right site →
  plaquetteCrossCharge fieldValue left right site
  ≡ (+ 3 / 1) * plaquetteDiagonalCharge fieldValue left right site
plaquetteCrossChargeIsThreeDiagonal fieldValue left right site =
  ℚRing.solve-∀
    (plaquetteSlotCharge fieldValue left right site Placement.slot0)
    (plaquetteSlotCharge fieldValue left right site Placement.slot1)
    (plaquetteSlotCharge fieldValue left right site Placement.slot2)
    (plaquetteSlotCharge fieldValue left right site Placement.slot3)

pairDiagonalIncidence :
  Coordinates.PhysicalSU2BondField4 →
  Periodic.Axis4 → Periodic.Axis4 → ℚ
pairDiagonalIncidence fieldValue left right =
  Periodic.sumSites (plaquetteDiagonalCharge fieldValue left right)

pairCrossIncidence :
  Coordinates.PhysicalSU2BondField4 →
  Periodic.Axis4 → Periodic.Axis4 → ℚ
pairCrossIncidence fieldValue left right =
  Periodic.sumSites (plaquetteCrossCharge fieldValue left right)

pairDiagonalIncidenceRaw : ∀ fieldValue left right →
  pairDiagonalIncidence fieldValue left right
  ≡ Global.axisInsertionNormSq fieldValue left
    + Global.axisInsertionNormSq fieldValue right
    + Global.axisInsertionNormSq fieldValue left
    + Global.axisInsertionNormSq fieldValue right
pairDiagonalIncidenceRaw fieldValue left right =
  let
    leftTerm = linkInsertionCharge fieldValue left
    rightTerm = linkInsertionCharge fieldValue right

    expanded =
      Periodic.sumSitesCong
        (plaquetteDiagonalCharge fieldValue left right)
        (λ site →
          leftTerm site
          + rightTerm (Periodic.shiftForward left site)
          + leftTerm (Periodic.shiftForward right site)
          + rightTerm site)
        (plaquetteDiagonalChargeExpanded fieldValue left right)

    split0 =
      Periodic.sumSitesAdd
        leftTerm
        (λ site →
          rightTerm (Periodic.shiftForward left site)
          + leftTerm (Periodic.shiftForward right site)
          + rightTerm site)

    split1 =
      Periodic.sumSitesAdd
        (λ site → rightTerm (Periodic.shiftForward left site))
        (λ site →
          leftTerm (Periodic.shiftForward right site)
          + rightTerm site)

    split2 =
      Periodic.sumSitesAdd
        (λ site → leftTerm (Periodic.shiftForward right site))
        rightTerm

    shiftedRight = Periodic.sumSitesForwardInvariant rightTerm left
    shiftedLeft = Periodic.sumSitesForwardInvariant leftTerm right
  in
  trans expanded
    (trans split0
      (cong₂ _+_ refl
        (trans split1
          (trans
            (cong₂ _+_ shiftedRight
              (trans split2
                (cong₂ _+_ shiftedLeft refl)))
            (ℚRing.solve-∀
              (Periodic.sumSites leftTerm)
              (Periodic.sumSites rightTerm))))))

pairDiagonalIncidenceExact : ∀ fieldValue left right →
  pairDiagonalIncidence fieldValue left right
  ≡ (+ 2 / 1)
      * (Global.axisInsertionNormSq fieldValue left
        + Global.axisInsertionNormSq fieldValue right)
pairDiagonalIncidenceExact fieldValue left right =
  trans
    (pairDiagonalIncidenceRaw fieldValue left right)
    (ℚRing.solve-∀
      (Global.axisInsertionNormSq fieldValue left)
      (Global.axisInsertionNormSq fieldValue right))

pairCrossIncidenceIsThreeDiagonal : ∀ fieldValue left right →
  pairCrossIncidence fieldValue left right
  ≡ (+ 3 / 1) * pairDiagonalIncidence fieldValue left right
pairCrossIncidenceIsThreeDiagonal fieldValue left right =
  trans
    (Periodic.sumSitesCong
      (plaquetteCrossCharge fieldValue left right)
      (λ site →
        (+ 3 / 1) * plaquetteDiagonalCharge fieldValue left right site)
      (plaquetteCrossChargeIsThreeDiagonal fieldValue left right))
    (Periodic.sumSitesScale
      (+ 3 / 1) (plaquetteDiagonalCharge fieldValue left right))

physicalWilsonDiagonalIncidence :
  Coordinates.PhysicalSU2BondField4 → ℚ
physicalWilsonDiagonalIncidence fieldValue =
  pairDiagonalIncidence fieldValue Periodic.axis0 Periodic.axis1
  + pairDiagonalIncidence fieldValue Periodic.axis0 Periodic.axis2
  + pairDiagonalIncidence fieldValue Periodic.axis0 Periodic.axis3
  + pairDiagonalIncidence fieldValue Periodic.axis1 Periodic.axis2
  + pairDiagonalIncidence fieldValue Periodic.axis1 Periodic.axis3
  + pairDiagonalIncidence fieldValue Periodic.axis2 Periodic.axis3

physicalWilsonCrossIncidence :
  Coordinates.PhysicalSU2BondField4 → ℚ
physicalWilsonCrossIncidence fieldValue =
  pairCrossIncidence fieldValue Periodic.axis0 Periodic.axis1
  + pairCrossIncidence fieldValue Periodic.axis0 Periodic.axis2
  + pairCrossIncidence fieldValue Periodic.axis0 Periodic.axis3
  + pairCrossIncidence fieldValue Periodic.axis1 Periodic.axis2
  + pairCrossIncidence fieldValue Periodic.axis1 Periodic.axis3
  + pairCrossIncidence fieldValue Periodic.axis2 Periodic.axis3

physicalWilsonDiagonalIncidencePeriodicExact : ∀ fieldValue →
  physicalWilsonDiagonalIncidence fieldValue
  ≡ (+ 6 / 1) * Global.periodicPhysicalBondNormSq fieldValue
physicalWilsonDiagonalIncidencePeriodicExact fieldValue
  rewrite pairDiagonalIncidenceExact fieldValue Periodic.axis0 Periodic.axis1
        | pairDiagonalIncidenceExact fieldValue Periodic.axis0 Periodic.axis2
        | pairDiagonalIncidenceExact fieldValue Periodic.axis0 Periodic.axis3
        | pairDiagonalIncidenceExact fieldValue Periodic.axis1 Periodic.axis2
        | pairDiagonalIncidenceExact fieldValue Periodic.axis1 Periodic.axis3
        | pairDiagonalIncidenceExact fieldValue Periodic.axis2 Periodic.axis3 =
  ℚRing.solve-∀
    (Global.axisInsertionNormSq fieldValue Periodic.axis0)
    (Global.axisInsertionNormSq fieldValue Periodic.axis1)
    (Global.axisInsertionNormSq fieldValue Periodic.axis2)
    (Global.axisInsertionNormSq fieldValue Periodic.axis3)

physicalWilsonDiagonalIncidenceExact : ∀ fieldValue →
  physicalWilsonDiagonalIncidence fieldValue
  ≡ (+ 6 / 1) * Coordinates.physicalSU2BondNormSq fieldValue
physicalWilsonDiagonalIncidenceExact fieldValue =
  trans
    (physicalWilsonDiagonalIncidencePeriodicExact fieldValue)
    (cong ((+ 6 / 1) *_)
      (Global.periodicPhysicalBondNormSqExact fieldValue))

physicalWilsonCrossIncidenceIsThreeDiagonal : ∀ fieldValue →
  physicalWilsonCrossIncidence fieldValue
  ≡ (+ 3 / 1) * physicalWilsonDiagonalIncidence fieldValue
physicalWilsonCrossIncidenceIsThreeDiagonal fieldValue
  rewrite pairCrossIncidenceIsThreeDiagonal
      fieldValue Periodic.axis0 Periodic.axis1
        | pairCrossIncidenceIsThreeDiagonal
      fieldValue Periodic.axis0 Periodic.axis2
        | pairCrossIncidenceIsThreeDiagonal
      fieldValue Periodic.axis0 Periodic.axis3
        | pairCrossIncidenceIsThreeDiagonal
      fieldValue Periodic.axis1 Periodic.axis2
        | pairCrossIncidenceIsThreeDiagonal
      fieldValue Periodic.axis1 Periodic.axis3
        | pairCrossIncidenceIsThreeDiagonal
      fieldValue Periodic.axis2 Periodic.axis3 =
  ℚRing.solve-∀
    (pairDiagonalIncidence fieldValue Periodic.axis0 Periodic.axis1)
    (pairDiagonalIncidence fieldValue Periodic.axis0 Periodic.axis2)
    (pairDiagonalIncidence fieldValue Periodic.axis0 Periodic.axis3)
    (pairDiagonalIncidence fieldValue Periodic.axis1 Periodic.axis2)
    (pairDiagonalIncidence fieldValue Periodic.axis1 Periodic.axis3)
    (pairDiagonalIncidence fieldValue Periodic.axis2 Periodic.axis3)

physicalWilsonCrossIncidenceExact : ∀ fieldValue →
  physicalWilsonCrossIncidence fieldValue
  ≡ (+ 18 / 1) * Coordinates.physicalSU2BondNormSq fieldValue
physicalWilsonCrossIncidenceExact fieldValue =
  trans
    (physicalWilsonCrossIncidenceIsThreeDiagonal fieldValue)
    (trans
      (cong ((+ 3 / 1) *_)
        (physicalWilsonDiagonalIncidenceExact fieldValue))
      (ℚRing.solve-∀
        (Coordinates.physicalSU2BondNormSq fieldValue)))

physicalWilsonLocalChargeEnumerationLevel : ProofLevel
physicalWilsonLocalChargeEnumerationLevel = machineChecked

physicalWilsonDiagonalIncidenceLevel : ProofLevel
physicalWilsonDiagonalIncidenceLevel = machineChecked

physicalWilsonCrossIncidenceLevel : ProofLevel
physicalWilsonCrossIncidenceLevel = machineChecked
