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
linkInsertionCharge field axis site =
  Norm.normSq (Gauge.insertionQuaternion field axis site)

plaquetteSlotCharge :
  Coordinates.PhysicalSU2BondField4 →
  Periodic.Axis4 → Periodic.Axis4 → Periodic.Site4 →
  Placement.PlaquetteLinkSlot4 → ℚ
plaquetteSlotCharge field left right site Placement.slot0 =
  linkInsertionCharge field left site
plaquetteSlotCharge field left right site Placement.slot1 =
  linkInsertionCharge field right (Periodic.shiftForward left site)
plaquetteSlotCharge field left right site Placement.slot2 =
  linkInsertionCharge field left (Periodic.shiftForward right site)
plaquetteSlotCharge field left right site Placement.slot3 =
  linkInsertionCharge field right site

plaquetteDiagonalCharge :
  Coordinates.PhysicalSU2BondField4 →
  Periodic.Axis4 → Periodic.Axis4 → Periodic.Site4 → ℚ
plaquetteDiagonalCharge field left right site =
  Sums.sumRational Placement.plaquetteLinkSlots4
    (plaquetteSlotCharge field left right site)

orderedCrossCharge :
  Coordinates.PhysicalSU2BondField4 →
  Periodic.Axis4 → Periodic.Axis4 → Periodic.Site4 →
  Placement.OrderedDistinctSlotPair4 → ℚ
orderedCrossCharge field left right site pair =
  (+ 1 / 2)
    * (plaquetteSlotCharge field left right site
        (Placement.orderedPairFirst pair)
      + plaquetteSlotCharge field left right site
        (Placement.orderedPairSecond pair))

plaquetteCrossCharge :
  Coordinates.PhysicalSU2BondField4 →
  Periodic.Axis4 → Periodic.Axis4 → Periodic.Site4 → ℚ
plaquetteCrossCharge field left right site =
  Sums.sumRational Placement.orderedDistinctSlotPairs4
    (orderedCrossCharge field left right site)

plaquetteDiagonalChargeExpanded : ∀ field left right site →
  plaquetteDiagonalCharge field left right site
  ≡ linkInsertionCharge field left site
    + linkInsertionCharge field right (Periodic.shiftForward left site)
    + linkInsertionCharge field left (Periodic.shiftForward right site)
    + linkInsertionCharge field right site
plaquetteDiagonalChargeExpanded field left right site =
  ℚRing.solve-∀
    (linkInsertionCharge field left site)
    (linkInsertionCharge field right (Periodic.shiftForward left site))
    (linkInsertionCharge field left (Periodic.shiftForward right site))
    (linkInsertionCharge field right site)

plaquetteCrossChargeIsThreeDiagonal : ∀ field left right site →
  plaquetteCrossCharge field left right site
  ≡ (+ 3 / 1) * plaquetteDiagonalCharge field left right site
plaquetteCrossChargeIsThreeDiagonal field left right site =
  ℚRing.solve-∀
    (plaquetteSlotCharge field left right site Placement.slot0)
    (plaquetteSlotCharge field left right site Placement.slot1)
    (plaquetteSlotCharge field left right site Placement.slot2)
    (plaquetteSlotCharge field left right site Placement.slot3)

pairDiagonalIncidence :
  Coordinates.PhysicalSU2BondField4 →
  Periodic.Axis4 → Periodic.Axis4 → ℚ
pairDiagonalIncidence field left right =
  Periodic.sumSites (plaquetteDiagonalCharge field left right)

pairCrossIncidence :
  Coordinates.PhysicalSU2BondField4 →
  Periodic.Axis4 → Periodic.Axis4 → ℚ
pairCrossIncidence field left right =
  Periodic.sumSites (plaquetteCrossCharge field left right)

pairDiagonalIncidenceRaw : ∀ field left right →
  pairDiagonalIncidence field left right
  ≡ Global.axisInsertionNormSq field left
    + Global.axisInsertionNormSq field right
    + Global.axisInsertionNormSq field left
    + Global.axisInsertionNormSq field right
pairDiagonalIncidenceRaw field left right =
  let
    leftTerm = linkInsertionCharge field left
    rightTerm = linkInsertionCharge field right

    expanded =
      Periodic.sumSitesCong
        (plaquetteDiagonalCharge field left right)
        (λ site →
          leftTerm site
          + rightTerm (Periodic.shiftForward left site)
          + leftTerm (Periodic.shiftForward right site)
          + rightTerm site)
        (plaquetteDiagonalChargeExpanded field left right)

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

pairDiagonalIncidenceExact : ∀ field left right →
  pairDiagonalIncidence field left right
  ≡ (+ 2 / 1)
      * (Global.axisInsertionNormSq field left
        + Global.axisInsertionNormSq field right)
pairDiagonalIncidenceExact field left right =
  trans
    (pairDiagonalIncidenceRaw field left right)
    (ℚRing.solve-∀
      (Global.axisInsertionNormSq field left)
      (Global.axisInsertionNormSq field right))

pairCrossIncidenceIsThreeDiagonal : ∀ field left right →
  pairCrossIncidence field left right
  ≡ (+ 3 / 1) * pairDiagonalIncidence field left right
pairCrossIncidenceIsThreeDiagonal field left right =
  trans
    (Periodic.sumSitesCong
      (plaquetteCrossCharge field left right)
      (λ site →
        (+ 3 / 1) * plaquetteDiagonalCharge field left right site)
      (plaquetteCrossChargeIsThreeDiagonal field left right))
    (Periodic.sumSitesScale
      (+ 3 / 1) (plaquetteDiagonalCharge field left right))

physicalWilsonDiagonalIncidence :
  Coordinates.PhysicalSU2BondField4 → ℚ
physicalWilsonDiagonalIncidence field =
  pairDiagonalIncidence field Periodic.axis0 Periodic.axis1
  + pairDiagonalIncidence field Periodic.axis0 Periodic.axis2
  + pairDiagonalIncidence field Periodic.axis0 Periodic.axis3
  + pairDiagonalIncidence field Periodic.axis1 Periodic.axis2
  + pairDiagonalIncidence field Periodic.axis1 Periodic.axis3
  + pairDiagonalIncidence field Periodic.axis2 Periodic.axis3

physicalWilsonCrossIncidence :
  Coordinates.PhysicalSU2BondField4 → ℚ
physicalWilsonCrossIncidence field =
  pairCrossIncidence field Periodic.axis0 Periodic.axis1
  + pairCrossIncidence field Periodic.axis0 Periodic.axis2
  + pairCrossIncidence field Periodic.axis0 Periodic.axis3
  + pairCrossIncidence field Periodic.axis1 Periodic.axis2
  + pairCrossIncidence field Periodic.axis1 Periodic.axis3
  + pairCrossIncidence field Periodic.axis2 Periodic.axis3

physicalWilsonDiagonalIncidencePeriodicExact : ∀ field →
  physicalWilsonDiagonalIncidence field
  ≡ (+ 6 / 1) * Global.periodicPhysicalBondNormSq field
physicalWilsonDiagonalIncidencePeriodicExact field
  rewrite pairDiagonalIncidenceExact field Periodic.axis0 Periodic.axis1
        | pairDiagonalIncidenceExact field Periodic.axis0 Periodic.axis2
        | pairDiagonalIncidenceExact field Periodic.axis0 Periodic.axis3
        | pairDiagonalIncidenceExact field Periodic.axis1 Periodic.axis2
        | pairDiagonalIncidenceExact field Periodic.axis1 Periodic.axis3
        | pairDiagonalIncidenceExact field Periodic.axis2 Periodic.axis3 =
  ℚRing.solve-∀
    (Global.axisInsertionNormSq field Periodic.axis0)
    (Global.axisInsertionNormSq field Periodic.axis1)
    (Global.axisInsertionNormSq field Periodic.axis2)
    (Global.axisInsertionNormSq field Periodic.axis3)

physicalWilsonDiagonalIncidenceExact : ∀ field →
  physicalWilsonDiagonalIncidence field
  ≡ (+ 6 / 1) * Coordinates.physicalSU2BondNormSq field
physicalWilsonDiagonalIncidenceExact field =
  trans
    (physicalWilsonDiagonalIncidencePeriodicExact field)
    (cong ((+ 6 / 1) *_)
      (Global.periodicPhysicalBondNormSqExact field))

physicalWilsonCrossIncidenceIsThreeDiagonal : ∀ field →
  physicalWilsonCrossIncidence field
  ≡ (+ 3 / 1) * physicalWilsonDiagonalIncidence field
physicalWilsonCrossIncidenceIsThreeDiagonal field
  rewrite pairCrossIncidenceIsThreeDiagonal
      field Periodic.axis0 Periodic.axis1
        | pairCrossIncidenceIsThreeDiagonal
      field Periodic.axis0 Periodic.axis2
        | pairCrossIncidenceIsThreeDiagonal
      field Periodic.axis0 Periodic.axis3
        | pairCrossIncidenceIsThreeDiagonal
      field Periodic.axis1 Periodic.axis2
        | pairCrossIncidenceIsThreeDiagonal
      field Periodic.axis1 Periodic.axis3
        | pairCrossIncidenceIsThreeDiagonal
      field Periodic.axis2 Periodic.axis3 =
  ℚRing.solve-∀
    (pairDiagonalIncidence field Periodic.axis0 Periodic.axis1)
    (pairDiagonalIncidence field Periodic.axis0 Periodic.axis2)
    (pairDiagonalIncidence field Periodic.axis0 Periodic.axis3)
    (pairDiagonalIncidence field Periodic.axis1 Periodic.axis2)
    (pairDiagonalIncidence field Periodic.axis1 Periodic.axis3)
    (pairDiagonalIncidence field Periodic.axis2 Periodic.axis3)

physicalWilsonCrossIncidenceExact : ∀ field →
  physicalWilsonCrossIncidence field
  ≡ (+ 18 / 1) * Coordinates.physicalSU2BondNormSq field
physicalWilsonCrossIncidenceExact field =
  trans
    (physicalWilsonCrossIncidenceIsThreeDiagonal field)
    (trans
      (cong ((+ 3 / 1) *_)
        (physicalWilsonDiagonalIncidenceExact field))
      (ℚRing.solve-∀
        (Coordinates.physicalSU2BondNormSq field)))

physicalWilsonLocalChargeEnumerationLevel : ProofLevel
physicalWilsonLocalChargeEnumerationLevel = machineChecked

physicalWilsonDiagonalIncidenceLevel : ProofLevel
physicalWilsonDiagonalIncidenceLevel = machineChecked

physicalWilsonCrossIncidenceLevel : ProofLevel
physicalWilsonCrossIncidenceLevel = machineChecked
