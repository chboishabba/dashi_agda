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
-- The literal four plaquette boundary cells are pairwise distinct.  Hence the
-- Boolean-subset localization is an additive four-slot set function.  For every
-- physical vector v and plaquette p, summing the subset projections over each
-- cardinality layer gives exactly
--
--   L1 = P_p v,
--   L2 = 3 P_p v,
--   L3 = 3 P_p v,
--   L4 = P_p v.
--
-- Substitution into the repository's exact Rota/Möbius degree formulas gives
-- D2=D3=D4=0.  Thus both the source and defect localization families can carry
-- only degree one into the KKT Green contraction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _/_)
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
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanSelectedConstraintAtomGreenExpansionExact as Green
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums

emptyElim : ∀ {A : Set} → Empty → A
emptyElim ()

sumRationalZero : ∀ {A : Set} (values : List A) →
  Sums.sumRational values (λ _ → 0ℚ) ≡ 0ℚ
sumRationalZero [] = refl
sumRationalZero (value ∷ values)
  rewrite sumRationalZero values = ℚRing.solve []

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
-- Truth-table normalization when exactly one boundary slot can match.
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
-- One-coordinate subset-mask reductions.
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

boundaryMaskOutside : ∀ plaquette coordinate →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell0 plaquette →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell1 plaquette →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell2 plaquette →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell3 plaquette →
  Boundary.plaquetteBoundaryMask plaquette coordinate ≡ false
boundaryMaskOutside plaquette coordinate ne0 ne1 ne2 ne3
  rewrite bondCellEqualFalse ne0
        | bondCellEqualFalse ne1
        | bondCellEqualFalse ne2
        | bondCellEqualFalse ne3 = refl

boundaryProjectAt0 : ∀ plaquette vector coordinate →
  Boundary.physicalCoordinateCell coordinate ≡ Boundary.boundaryCell0 plaquette →
  Boundary.plaquetteBoundaryProject plaquette vector coordinate ≡ vector coordinate
boundaryProjectAt0 plaquette vector coordinate eq0 =
  trans
    (cong (λ selected → Projector.maskSelect selected (vector coordinate))
      (Boundary.plaquetteBoundaryMaskAt0 plaquette coordinate eq0))
    (ℚRing.solve-∀ (vector coordinate))

boundaryProjectAt1 : ∀ plaquette vector coordinate →
  Boundary.physicalCoordinateCell coordinate ≡ Boundary.boundaryCell1 plaquette →
  Boundary.plaquetteBoundaryProject plaquette vector coordinate ≡ vector coordinate
boundaryProjectAt1 plaquette vector coordinate eq1 =
  trans
    (cong (λ selected → Projector.maskSelect selected (vector coordinate))
      (Boundary.plaquetteBoundaryMaskAt1 plaquette coordinate eq1))
    (ℚRing.solve-∀ (vector coordinate))

boundaryProjectAt2 : ∀ plaquette vector coordinate →
  Boundary.physicalCoordinateCell coordinate ≡ Boundary.boundaryCell2 plaquette →
  Boundary.plaquetteBoundaryProject plaquette vector coordinate ≡ vector coordinate
boundaryProjectAt2 plaquette vector coordinate eq2 =
  trans
    (cong (λ selected → Projector.maskSelect selected (vector coordinate))
      (Boundary.plaquetteBoundaryMaskAt2 plaquette coordinate eq2))
    (ℚRing.solve-∀ (vector coordinate))

boundaryProjectAt3 : ∀ plaquette vector coordinate →
  Boundary.physicalCoordinateCell coordinate ≡ Boundary.boundaryCell3 plaquette →
  Boundary.plaquetteBoundaryProject plaquette vector coordinate ≡ vector coordinate
boundaryProjectAt3 plaquette vector coordinate eq3 =
  trans
    (cong (λ selected → Projector.maskSelect selected (vector coordinate))
      (Boundary.plaquetteBoundaryMaskAt3 plaquette coordinate eq3))
    (ℚRing.solve-∀ (vector coordinate))

boundaryProjectOutside : ∀ plaquette vector coordinate →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell0 plaquette →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell1 plaquette →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell2 plaquette →
  Boundary.physicalCoordinateCell coordinate ≢ Boundary.boundaryCell3 plaquette →
  Boundary.plaquetteBoundaryProject plaquette vector coordinate ≡ 0ℚ
boundaryProjectOutside plaquette vector coordinate ne0 ne1 ne2 ne3 =
  trans
    (cong (λ selected → Projector.maskSelect selected (vector coordinate))
      (boundaryMaskOutside plaquette coordinate ne0 ne1 ne2 ne3))
    (ℚRing.solve-∀ (vector coordinate))

------------------------------------------------------------------------
-- Fixed-cardinality subset layers.
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
  Projector.PhysicalVector → Plaquette.Plaquette4 →
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
      (λ subset →
        cong (λ selected → Projector.maskSelect selected (vector coordinate))
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
    (sumRationalZero (Degree.degreeSubsets degree))

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
    (cong (layerCoefficient degree *_)
      (sym (boundaryProjectAt0 plaquette vector coordinate eq0)))
... | no ne0 | yes eq1 | yes eq2 | d3 =
  emptyElim (Distinct.boundaryCell1Not2 plaquette (trans (sym eq1) eq2))
... | no ne0 | yes eq1 | no ne2 | yes eq3 =
  emptyElim (Distinct.boundaryCell1Not3 plaquette (trans (sym eq1) eq3))
... | no ne0 | yes eq1 | no ne2 | no ne3 =
  trans
    (sumProjectsAtSlot Cube.slot1 vector plaquette degree coordinate
      (λ subset → maskAt1 subset plaquette coordinate ne0 eq1 ne2 ne3))
    (cong (layerCoefficient degree *_)
      (sym (boundaryProjectAt1 plaquette vector coordinate eq1)))
... | no ne0 | no ne1 | yes eq2 | yes eq3 =
  emptyElim (Distinct.boundaryCell2Not3 plaquette (trans (sym eq2) eq3))
... | no ne0 | no ne1 | yes eq2 | no ne3 =
  trans
    (sumProjectsAtSlot Cube.slot2 vector plaquette degree coordinate
      (λ subset → maskAt2 subset plaquette coordinate ne0 ne1 eq2 ne3))
    (cong (layerCoefficient degree *_)
      (sym (boundaryProjectAt2 plaquette vector coordinate eq2)))
... | no ne0 | no ne1 | no ne2 | yes eq3 =
  trans
    (sumProjectsAtSlot Cube.slot3 vector plaquette degree coordinate
      (λ subset → maskAt3 subset plaquette coordinate ne0 ne1 ne2 eq3))
    (cong (layerCoefficient degree *_)
      (sym (boundaryProjectAt3 plaquette vector coordinate eq3)))
... | no ne0 | no ne1 | no ne2 | no ne3 =
  trans
    (sumProjectsOutside vector plaquette degree coordinate
      (λ subset → maskOutside subset plaquette coordinate ne0 ne1 ne2 ne3))
    (trans
      (ℚRing.solve-∀ (layerCoefficient degree))
      (cong (layerCoefficient degree *_)
        (sym (boundaryProjectOutside
          plaquette vector coordinate ne0 ne1 ne2 ne3))))

------------------------------------------------------------------------
-- Clean layer identities.  The actual D2/D3/D4 cancellation is consumed by
-- the canonical source/defect state module, whose degree definitions are
-- L2-3L1, L3-2L2+3L1, and L4-L3+L2-L1 respectively.
------------------------------------------------------------------------

layer1IsBoundary : ∀ vector plaquette coordinate →
  subsetLayerState vector plaquette Degree.degree1 coordinate
  ≡ Boundary.plaquetteBoundaryProject plaquette vector coordinate
layer1IsBoundary vector plaquette coordinate =
  trans
    (subsetLayerStateCoefficientExact vector plaquette Degree.degree1 coordinate)
    (ℚRing.solve-∀ (Boundary.plaquetteBoundaryProject plaquette vector coordinate))

layer2IsThreeLayer1 : ∀ vector plaquette coordinate →
  subsetLayerState vector plaquette Degree.degree2 coordinate
  ≡ (+ 3 / 1) * subsetLayerState vector plaquette Degree.degree1 coordinate
layer2IsThreeLayer1 vector plaquette coordinate =
  trans
    (subsetLayerStateCoefficientExact vector plaquette Degree.degree2 coordinate)
    (cong ((+ 3 / 1) *_)
      (sym (layer1IsBoundary vector plaquette coordinate)))

layer3IsThreeLayer1 : ∀ vector plaquette coordinate →
  subsetLayerState vector plaquette Degree.degree3 coordinate
  ≡ (+ 3 / 1) * subsetLayerState vector plaquette Degree.degree1 coordinate
layer3IsThreeLayer1 vector plaquette coordinate =
  trans
    (subsetLayerStateCoefficientExact vector plaquette Degree.degree3 coordinate)
    (cong ((+ 3 / 1) *_)
      (sym (layer1IsBoundary vector plaquette coordinate)))

layer4IsLayer1 : ∀ vector plaquette coordinate →
  subsetLayerState vector plaquette Degree.degree4 coordinate
  ≡ subsetLayerState vector plaquette Degree.degree1 coordinate
layer4IsLayer1 vector plaquette coordinate =
  trans
    (subsetLayerStateCoefficientExact vector plaquette Degree.degree4 coordinate)
    (trans
      (ℚRing.solve-∀
        (Boundary.plaquetteBoundaryProject plaquette vector coordinate))
      (sym (layer1IsBoundary vector plaquette coordinate)))

plaquetteSubsetMobiusDegreeOneCollapseLevel : ProofLevel
plaquetteSubsetMobiusDegreeOneCollapseLevel = machineChecked
