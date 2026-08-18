module DASHI.Physics.YangMills.BalabanPlaquetteSubsetMobiusDegreeOneCollapseExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Gian-Carlo Rota,
-- "On the Foundations of Combinatorial Theory I. Theory of Möbius
-- Functions", Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte
-- Gebiete 2 (1964), 340--368.
-- DOI: 10.1007/BF00531932.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- DASHI CONTRIBUTION
--
-- Use the literal pairwise-distinct plaquette boundary geometry to prove that
-- the Boolean-subset localization is an additive four-slot set function.
-- For every physical vector v and plaquette p, the sums over subsets of fixed
-- cardinality are exactly
--
--   L1 = P_p v,
--   L2 = 3 P_p v,
--   L3 = 3 P_p v,
--   L4 = P_p v.
--
-- Therefore the Rota/Mobius degree states satisfy D2=D3=D4=0 exactly.  This
-- removes twelve source/defect Green degree blocks from the physical G2 route:
-- only degree one can survive for either the Wilson first variation or the raw
-- plaquette extractor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (Empty; _≢_; yes; no)
import DASHI.Physics.YangMills.BalabanP33LiteralResidualKernelNumericalCalibrationExact as Calibration
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateProjectorExact as Projector
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanP33PlaquetteSubsetProjectorExact as Subset
import DASHI.Physics.YangMills.BalabanPlaquetteBoundaryCellsPairwiseDistinctExact as Distinct
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanSelectedConstraintAtomGreenExpansionExact as Green
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums

emptyElim : ∀ {A : Set} → Empty → A
emptyElim ()

bondCellEqualTrue : ∀ {left right} →
  left ≡ right → Boundary.bondCellEqual left right ≡ true
bondCellEqualTrue {left} refl = Boundary.bondCellEqualRefl left

bondCellEqualFalse : ∀ {left right} →
  left ≢ right → Boundary.bondCellEqual left right ≡ false
bondCellEqualFalse {left} {right} notEqual
  with Calibration.bondCellDecidableEquality left right
... | yes equality = emptyElim (notEqual equality)
... | no _ = refl

------------------------------------------------------------------------
-- Boolean normalization when at most one boundary slot matches.
------------------------------------------------------------------------

only0 : ∀ subset →
  Subset._or_
    (Subset._and_ (Cube.contains Cube.slot0 subset) true)
    (Subset._or_
      (Subset._and_ (Cube.contains Cube.slot1 subset) false)
      (Subset._or_
        (Subset._and_ (Cube.contains Cube.slot2 subset) false)
        (Subset._and_ (Cube.contains Cube.slot3 subset) false)))
  ≡ Cube.contains Cube.slot0 subset
only0 Cube.empty = refl
only0 Cube.s0 = refl
only0 Cube.s1 = refl
only0 Cube.s2 = refl
only0 Cube.s3 = refl
only0 Cube.s01 = refl
only0 Cube.s02 = refl
only0 Cube.s03 = refl
only0 Cube.s12 = refl
only0 Cube.s13 = refl
only0 Cube.s23 = refl
only0 Cube.s012 = refl
only0 Cube.s013 = refl
only0 Cube.s023 = refl
only0 Cube.s123 = refl
only0 Cube.s0123 = refl

only1 : ∀ subset →
  Subset._or_
    (Subset._and_ (Cube.contains Cube.slot0 subset) false)
    (Subset._or_
      (Subset._and_ (Cube.contains Cube.slot1 subset) true)
      (Subset._or_
        (Subset._and_ (Cube.contains Cube.slot2 subset) false)
        (Subset._and_ (Cube.contains Cube.slot3 subset) false)))
  ≡ Cube.contains Cube.slot1 subset
only1 Cube.empty = refl
only1 Cube.s0 = refl
only1 Cube.s1 = refl
only1 Cube.s2 = refl
only1 Cube.s3 = refl
only1 Cube.s01 = refl
only1 Cube.s02 = refl
only1 Cube.s03 = refl
only1 Cube.s12 = refl
only1 Cube.s13 = refl
only1 Cube.s23 = refl
only1 Cube.s012 = refl
only1 Cube.s013 = refl
only1 Cube.s023 = refl
only1 Cube.s123 = refl
only1 Cube.s0123 = refl

only2 : ∀ subset →
  Subset._or_
    (Subset._and_ (Cube.contains Cube.slot0 subset) false)
    (Subset._or_
      (Subset._and_ (Cube.contains Cube.slot1 subset) false)
      (Subset._or_
        (Subset._and_ (Cube.contains Cube.slot2 subset) true)
        (Subset._and_ (Cube.contains Cube.slot3 subset) false)))
  ≡ Cube.contains Cube.slot2 subset
only2 Cube.empty = refl
only2 Cube.s0 = refl
only2 Cube.s1 = refl
only2 Cube.s2 = refl
only2 Cube.s3 = refl
only2 Cube.s01 = refl
only2 Cube.s02 = refl
only2 Cube.s03 = refl
only2 Cube.s12 = refl
only2 Cube.s13 = refl
only2 Cube.s23 = refl
only2 Cube.s012 = refl
only2 Cube.s013 = refl
only2 Cube.s023 = refl
only2 Cube.s123 = refl
only2 Cube.s0123 = refl

only3 : ∀ subset →
  Subset._or_
    (Subset._and_ (Cube.contains Cube.slot0 subset) false)
    (Subset._or_
      (Subset._and_ (Cube.contains Cube.slot1 subset) false)
      (Subset._or_
        (Subset._and_ (Cube.contains Cube.slot2 subset) false)
        (Subset._and_ (Cube.contains Cube.slot3 subset) true)))
  ≡ Cube.contains Cube.slot3 subset
only3 Cube.empty = refl
only3 Cube.s0 = refl
only3 Cube.s1 = refl
only3 Cube.s2 = refl
only3 Cube.s3 = refl
only3 Cube.s01 = refl
only3 Cube.s02 = refl
only3 Cube.s03 = refl
only3 Cube.s12 = refl
only3 Cube.s13 = refl
only3 Cube.s23 = refl
only3 Cube.s012 = refl
only3 Cube.s013 = refl
only3 Cube.s023 = refl
only3 Cube.s123 = refl
only3 Cube.s0123 = refl

allFalse : ∀ subset →
  Subset._or_
    (Subset._and_ (Cube.contains Cube.slot0 subset) false)
    (Subset._or_
      (Subset._and_ (Cube.contains Cube.slot1 subset) false)
      (Subset._or_
        (Subset._and_ (Cube.contains Cube.slot2 subset) false)
        (Subset._and_ (Cube.contains Cube.slot3 subset) false)))
  ≡ false
allFalse Cube.empty = refl
allFalse Cube.s0 = refl
allFalse Cube.s1 = refl
allFalse Cube.s2 = refl
allFalse Cube.s3 = refl
allFalse Cube.s01 = refl
allFalse Cube.s02 = refl
allFalse Cube.s03 = refl
allFalse Cube.s12 = refl
allFalse Cube.s13 = refl
allFalse Cube.s23 = refl
allFalse Cube.s012 = refl
allFalse Cube.s013 = refl
allFalse Cube.s023 = refl
allFalse Cube.s123 = refl
allFalse Cube.s0123 = refl

------------------------------------------------------------------------
-- Subset masks reduce to exactly one membership bit on a boundary cell.
------------------------------------------------------------------------

maskAt0 : ∀ subset plaquette coordinate →
  Boundary.physicalCoordinateCell coordinate ≡ Boundary.boundaryCell0 plaquette →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell1 plaquette →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell2 plaquette →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell3 plaquette →
  Subset.subsetBoundaryMask subset plaquette coordinate
  ≡ Cube.contains Cube.slot0 subset
maskAt0 subset plaquette coordinate eq0 ne1 ne2 ne3
  rewrite bondCellEqualTrue eq0
        | bondCellEqualFalse ne1
        | bondCellEqualFalse ne2
        | bondCellEqualFalse ne3 = only0 subset

maskAt1 : ∀ subset plaquette coordinate →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell0 plaquette →
  Boundary.physicalCoordinateCell coordinate ≡ Boundary.boundaryCell1 plaquette →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell2 plaquette →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell3 plaquette →
  Subset.subsetBoundaryMask subset plaquette coordinate
  ≡ Cube.contains Cube.slot1 subset
maskAt1 subset plaquette coordinate ne0 eq1 ne2 ne3
  rewrite bondCellEqualFalse ne0
        | bondCellEqualTrue eq1
        | bondCellEqualFalse ne2
        | bondCellEqualFalse ne3 = only1 subset

maskAt2 : ∀ subset plaquette coordinate →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell0 plaquette →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell1 plaquette →
  Boundary.physicalCoordinateCell coordinate ≡ Boundary.boundaryCell2 plaquette →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell3 plaquette →
  Subset.subsetBoundaryMask subset plaquette coordinate
  ≡ Cube.contains Cube.slot2 subset
maskAt2 subset plaquette coordinate ne0 ne1 eq2 ne3
  rewrite bondCellEqualFalse ne0
        | bondCellEqualFalse ne1
        | bondCellEqualTrue eq2
        | bondCellEqualFalse ne3 = only2 subset

maskAt3 : ∀ subset plaquette coordinate →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell0 plaquette →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell1 plaquette →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell2 plaquette →
  Boundary.physicalCoordinateCell coordinate ≡ Boundary.boundaryCell3 plaquette →
  Subset.subsetBoundaryMask subset plaquette coordinate
  ≡ Cube.contains Cube.slot3 subset
maskAt3 subset plaquette coordinate ne0 ne1 ne2 eq3
  rewrite bondCellEqualFalse ne0
        | bondCellEqualFalse ne1
        | bondCellEqualFalse ne2
        | bondCellEqualTrue eq3 = only3 subset

maskOutside : ∀ subset plaquette coordinate →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell0 plaquette →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell1 plaquette →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell2 plaquette →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell3 plaquette →
  Subset.subsetBoundaryMask subset plaquette coordinate ≡ false
maskOutside subset plaquette coordinate ne0 ne1 ne2 ne3
  rewrite bondCellEqualFalse ne0
        | bondCellEqualFalse ne1
        | bondCellEqualFalse ne2
        | bondCellEqualFalse ne3 = allFalse subset

subsetProjectAtSlot : ∀ slot subset plaquette vector coordinate →
  (Subset.subsetBoundaryMask subset plaquette coordinate
    ≡ Cube.contains slot subset) →
  Subset.subsetBoundaryProject subset plaquette vector coordinate
  ≡ Projector.maskSelect (Cube.contains slot subset) (vector coordinate)
subsetProjectAtSlot slot subset plaquette vector coordinate maskExact =
  cong (λ selected → Projector.maskSelect selected (vector coordinate)) maskExact

------------------------------------------------------------------------
-- The number of d-subsets containing any fixed slot is 1,3,3,1.
------------------------------------------------------------------------

layerCoefficient : Degree.MobiusDegree → ℚ
layerCoefficient Degree.degree1 = + 1 / 1
layerCoefficient Degree.degree2 = + 3 / 1
layerCoefficient Degree.degree3 = + 3 / 1
layerCoefficient Degree.degree4 = + 1 / 1

membershipLayerCount : ∀ slot degree value →
  Sums.sumRational (Degree.degreeSubsets degree)
    (λ subset → Projector.maskSelect (Cube.contains slot subset) value)
  ≡ layerCoefficient degree * value
membershipLayerCount Cube.slot0 Degree.degree1 value = ℚRing.solve-∀ value
membershipLayerCount Cube.slot0 Degree.degree2 value = ℚRing.solve-∀ value
membershipLayerCount Cube.slot0 Degree.degree3 value = ℚRing.solve-∀ value
membershipLayerCount Cube.slot0 Degree.degree4 value = ℚRing.solve-∀ value
membershipLayerCount Cube.slot1 Degree.degree1 value = ℚRing.solve-∀ value
membershipLayerCount Cube.slot1 Degree.degree2 value = ℚRing.solve-∀ value
membershipLayerCount Cube.slot1 Degree.degree3 value = ℚRing.solve-∀ value
membershipLayerCount Cube.slot1 Degree.degree4 value = ℚRing.solve-∀ value
membershipLayerCount Cube.slot2 Degree.degree1 value = ℚRing.solve-∀ value
membershipLayerCount Cube.slot2 Degree.degree2 value = ℚRing.solve-∀ value
membershipLayerCount Cube.slot2 Degree.degree3 value = ℚRing.solve-∀ value
membershipLayerCount Cube.slot2 Degree.degree4 value = ℚRing.solve-∀ value
membershipLayerCount Cube.slot3 Degree.degree1 value = ℚRing.solve-∀ value
membershipLayerCount Cube.slot3 Degree.degree2 value = ℚRing.solve-∀ value
membershipLayerCount Cube.slot3 Degree.degree3 value = ℚRing.solve-∀ value
membershipLayerCount Cube.slot3 Degree.degree4 value = ℚRing.solve-∀ value

subsetLayerState :
  Projector.PhysicalVector →
  Boundary.Physical.Plaquette4 →
  Degree.MobiusDegree → Projector.PhysicalVector
subsetLayerState vector plaquette degree =
  Green.sumVector (Degree.degreeSubsets degree)
    (λ subset → Subset.subsetBoundaryProject subset plaquette vector)

sumProjectsAtSlot : ∀ slot vector plaquette degree coordinate →
  (∀ subset →
    Subset.subsetBoundaryMask subset plaquette coordinate
      ≡ Cube.contains slot subset) →
  subsetLayerState vector plaquette degree coordinate
  ≡ layerCoefficient degree * vector coordinate
sumProjectsAtSlot slot vector plaquette degree coordinate maskExact =
  trans
    (Sums.sumRationalCong
      (Degree.degreeSubsets degree)
      (λ subset → Subset.subsetBoundaryProject subset plaquette vector coordinate)
      (λ subset → Projector.maskSelect (Cube.contains slot subset) (vector coordinate))
      (λ subset → subsetProjectAtSlot slot subset plaquette vector coordinate
        (maskExact subset)))
    (membershipLayerCount slot degree (vector coordinate))

sumProjectsOutside : ∀ vector plaquette degree coordinate →
  (∀ subset → Subset.subsetBoundaryMask subset plaquette coordinate ≡ false) →
  subsetLayerState vector plaquette degree coordinate ≡ 0ℚ
sumProjectsOutside vector plaquette degree coordinate maskFalse =
  trans
    (Sums.sumRationalCong
      (Degree.degreeSubsets degree)
      (λ subset → Subset.subsetBoundaryProject subset plaquette vector coordinate)
      (λ subset → 0ℚ)
      (λ subset → trans
        (cong (λ selected → Projector.maskSelect selected (vector coordinate))
          (maskFalse subset))
        (ℚRing.solve-∀ (vector coordinate))))
    (Sums.sumRationalZero (Degree.degreeSubsets degree))

------------------------------------------------------------------------
-- Exact fixed-cardinality layer formula.
------------------------------------------------------------------------

subsetLayerStateCoefficientExact : ∀ vector plaquette degree coordinate →
  subsetLayerState vector plaquette degree coordinate
  ≡ layerCoefficient degree
      * Boundary.plaquetteBoundaryProject plaquette vector coordinate
subsetLayerStateCoefficientExact vector plaquette degree coordinate
  with Calibration.bondCellDecidableEquality
        (Boundary.physicalCoordinateCell coordinate)
        (Boundary.boundaryCell0 plaquette)
     | Calibration.bondCellDecidableEquality
        (Boundary.physicalCoordinateCell coordinate)
        (Boundary.boundaryCell1 plaquette)
     | Calibration.bondCellDecidableEquality
        (Boundary.physicalCoordinateCell coordinate)
        (Boundary.boundaryCell2 plaquette)
     | Calibration.bondCellDecidableEquality
        (Boundary.physicalCoordinateCell coordinate)
        (Boundary.boundaryCell3 plaquette)
... | yes eq0 | yes eq1 | d2 | d3 =
  emptyElim (Distinct.boundaryCell0Not1 plaquette (trans (sym eq0) eq1))
... | yes eq0 | no ne1 | yes eq2 | d3 =
  emptyElim (Distinct.boundaryCell0Not2 plaquette (trans (sym eq0) eq2))
... | yes eq0 | no ne1 | no ne2 | yes eq3 =
  emptyElim (Distinct.boundaryCell0Not3 plaquette (trans (sym eq0) eq3))
... | yes eq0 | no ne1 | no ne2 | no ne3 =
  trans
    (sumProjectsAtSlot Cube.slot0 vector plaquette degree coordinate
      (λ subset → maskAt0 subset plaquette coordinate eq0 ne1 ne2 ne3))
    (sym (cong (layerCoefficient degree *_)
      (Boundary.plaquetteBoundaryMaskAt0 plaquette coordinate eq0
       |> λ maskTrue → trans
          (cong (λ selected → Projector.maskSelect selected (vector coordinate)) maskTrue)
          (ℚRing.solve-∀ (vector coordinate)))))
... | no ne0 | yes eq1 | yes eq2 | d3 =
  emptyElim (Distinct.boundaryCell1Not2 plaquette (trans (sym eq1) eq2))
... | no ne0 | yes eq1 | no ne2 | yes eq3 =
  emptyElim (Distinct.boundaryCell1Not3 plaquette (trans (sym eq1) eq3))
... | no ne0 | yes eq1 | no ne2 | no ne3 =
  trans
    (sumProjectsAtSlot Cube.slot1 vector plaquette degree coordinate
      (λ subset → maskAt1 subset plaquette coordinate ne0 eq1 ne2 ne3))
    (sym (cong (layerCoefficient degree *_)
      (trans
        (cong (λ selected → Projector.maskSelect selected (vector coordinate))
          (Boundary.plaquetteBoundaryMaskAt1 plaquette coordinate eq1))
        (ℚRing.solve-∀ (vector coordinate)))))
... | no ne0 | no ne1 | yes eq2 | yes eq3 =
  emptyElim (Distinct.boundaryCell2Not3 plaquette (trans (sym eq2) eq3))
... | no ne0 | no ne1 | yes eq2 | no ne3 =
  trans
    (sumProjectsAtSlot Cube.slot2 vector plaquette degree coordinate
      (λ subset → maskAt2 subset plaquette coordinate ne0 ne1 eq2 ne3))
    (sym (cong (layerCoefficient degree *_)
      (trans
        (cong (λ selected → Projector.maskSelect selected (vector coordinate))
          (Boundary.plaquetteBoundaryMaskAt2 plaquette coordinate eq2))
        (ℚRing.solve-∀ (vector coordinate)))))
... | no ne0 | no ne1 | no ne2 | yes eq3 =
  trans
    (sumProjectsAtSlot Cube.slot3 vector plaquette degree coordinate
      (λ subset → maskAt3 subset plaquette coordinate ne0 ne1 ne2 eq3))
    (sym (cong (layerCoefficient degree *_)
      (trans
        (cong (λ selected → Projector.maskSelect selected (vector coordinate))
          (Boundary.plaquetteBoundaryMaskAt3 plaquette coordinate eq3))
        (ℚRing.solve-∀ (vector coordinate)))))
... | no ne0 | no ne1 | no ne2 | no ne3 =
  trans
    (sumProjectsOutside vector plaquette degree coordinate
      (λ subset → maskOutside subset plaquette coordinate ne0 ne1 ne2 ne3))
    (sym (ℚRing.solve-∀
      (layerCoefficient degree)
      (Boundary.plaquetteBoundaryProject plaquette vector coordinate)))

------------------------------------------------------------------------
-- Clean layer identities and Mobius cancellation.
------------------------------------------------------------------------

layer1IsBoundary : ∀ vector plaquette coordinate →
  subsetLayerState vector plaquette Degree.degree1 coordinate
  ≡ Boundary.plaquetteBoundaryProject plaquette vector coordinate
layer1IsBoundary vector plaquette coordinate =
  trans (subsetLayerStateCoefficientExact vector plaquette Degree.degree1 coordinate)
    (ℚRing.solve-∀ (Boundary.plaquetteBoundaryProject plaquette vector coordinate))

layer2IsThreeLayer1 : ∀ vector plaquette coordinate →
  subsetLayerState vector plaquette Degree.degree2 coordinate
  ≡ (+ 3 / 1) * subsetLayerState vector plaquette Degree.degree1 coordinate
layer2IsThreeLayer1 vector plaquette coordinate =
  trans (subsetLayerStateCoefficientExact vector plaquette Degree.degree2 coordinate)
    (trans
      (cong ((+ 3 / 1) *_)
        (sym (layer1IsBoundary vector plaquette coordinate)))
      refl)

layer3IsThreeLayer1 : ∀ vector plaquette coordinate →
  subsetLayerState vector plaquette Degree.degree3 coordinate
  ≡ (+ 3 / 1) * subsetLayerState vector plaquette Degree.degree1 coordinate
layer3IsThreeLayer1 vector plaquette coordinate =
  trans (subsetLayerStateCoefficientExact vector plaquette Degree.degree3 coordinate)
    (cong ((+ 3 / 1) *_) (sym (layer1IsBoundary vector plaquette coordinate)))

layer4IsLayer1 : ∀ vector plaquette coordinate →
  subsetLayerState vector plaquette Degree.degree4 coordinate
  ≡ subsetLayerState vector plaquette Degree.degree1 coordinate
layer4IsLayer1 vector plaquette coordinate =
  trans (subsetLayerStateCoefficientExact vector plaquette Degree.degree4 coordinate)
    (trans
      (ℚRing.solve-∀ (Boundary.plaquetteBoundaryProject plaquette vector coordinate))
      (sym (layer1IsBoundary vector plaquette coordinate)))

plaquetteSubsetMobiusDegreeOneCollapseLevel : ProofLevel
plaquetteSubsetMobiusDegreeOneCollapseLevel = machineChecked
