module DASHI.Physics.YangMills.BalabanSelectedWilsonFirstVariationPlaquetteSupportExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Close the source-support half of the selected G2 construction on the literal
-- Wilson carrier.  The first-variation covector is NOT defined by projecting an
-- arbitrary vector and then calling it local.  Its coordinate at e_c is the
-- actual Wilson directional derivative on that physical coordinate basis:
--
--   g_p(c) = D S_p(A)[e_c].
--
-- If c is outside the four plaquette boundary bonds, every one of the twelve
-- local SU(2) insertion coordinates read by `plaquetteJetData` is zero.  Hence
-- all four factor-first jets vanish, the ordered first product vanishes, and
-- g_p(c)=0.  Therefore the actual basis-evaluated Wilson first variation lies
-- in the existing plaquette-boundary projector image and directly constructs
-- the existing LiteralSourceDefectSubsetProducer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (Product; pair; Empty; yes; no)
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Wilson
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonFirstVariationExact as First
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatWilsonCurlIdentificationExact as Flat
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanP33LiteralResidualKernelNumericalCalibrationExact as Calibration
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateProjectorExact as Projector
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanSelectedSourceSubsetConstraintPartialExact as SubsetSource

------------------------------------------------------------------------
-- Generic quaternion zero lemmas needed by the first-product recursion.
------------------------------------------------------------------------

quaternionMultiplyZeroLeft : ∀ value →
  Wilson.zeroQ Wilson.*q value ≡ Wilson.zeroQ
quaternionMultiplyZeroLeft (Wilson.quat a0 a1 a2 a3) =
  Wilson.quaternionExt
    (ℚRing.solve-∀ a0 a1 a2 a3)
    (ℚRing.solve-∀ a0 a1 a2 a3)
    (ℚRing.solve-∀ a0 a1 a2 a3)
    (ℚRing.solve-∀ a0 a1 a2 a3)

negPureZero :
  Wilson.negQ
    (Wilson.pureQuaternion (Wilson.vec3 0ℚ 0ℚ 0ℚ))
  ≡ Wilson.zeroQ
negPureZero =
  Wilson.quaternionExt
    (ℚRing.solve []) (ℚRing.solve []) (ℚRing.solve []) (ℚRing.solve [])

AllFirstZero : List Wilson.QuaternionFactorJet → Set
AllFirstZero [] = ⊤
AllFirstZero (factor ∷ factors) =
  (Wilson.factorFirst factor ≡ Wilson.zeroQ) × AllFirstZero factors

orderedFirstProductAllFirstZero : ∀ factors →
  AllFirstZero factors →
  Wilson.orderedFirstProduct factors ≡ Wilson.zeroQ
orderedFirstProductAllFirstZero [] tt = refl
orderedFirstProductAllFirstZero (factor ∷ factors) (headZero , tailZero) =
  let
    headTermZero :
      Wilson.factorFirst factor Wilson.*q Wilson.orderedValueProduct factors
      ≡ Wilson.zeroQ
    headTermZero =
      trans
        (cong
          (λ selected → selected Wilson.*q Wilson.orderedValueProduct factors)
          headZero)
        (quaternionMultiplyZeroLeft (Wilson.orderedValueProduct factors))

    tailProductZero :
      Wilson.orderedFirstProduct factors ≡ Wilson.zeroQ
    tailProductZero = orderedFirstProductAllFirstZero factors tailZero

    inheritedZero :
      Wilson.factorValue factor Wilson.*q Wilson.orderedFirstProduct factors
      ≡ Wilson.zeroQ
    inheritedZero =
      trans
        (cong (Wilson.factorValue factor Wilson.*q_) tailProductZero)
        (Wilson.quaternionMultiplyZeroRight (Wilson.factorValue factor))
  in
  trans
    (cong₂ Wilson._+q_ headTermZero inheritedZero)
    (Wilson.quaternionAddZeroLeft Wilson.zeroQ)

------------------------------------------------------------------------
-- A coordinate outside the boundary mask cannot hit any of the four cells.
------------------------------------------------------------------------

trueFalseImpossible : true ≡ false → Empty
trueFalseImpossible ()

basisAtBoundary0Zero :
  ∀ plaquette target coordinate →
  Boundary.plaquetteBoundaryMask plaquette target ≡ false →
  Basis.physicalBasis target
    (pair coordinate (Boundary.boundaryCell0 plaquette))
  ≡ 0ℚ
basisAtBoundary0Zero plaquette target coordinate maskFalse
  with Calibration.physicalCoordinateDecidableEquality
    (pair coordinate (Boundary.boundaryCell0 plaquette)) target
... | no _ = refl
... | yes exact =
  let
    targetCellExact :
      Boundary.physicalCoordinateCell target
      ≡ Boundary.boundaryCell0 plaquette
    targetCellExact =
      sym (cong Boundary.physicalCoordinateCell exact)
    maskTrue =
      Boundary.plaquetteBoundaryMaskAt0
        plaquette target targetCellExact
  in
  Boundary.emptyElim
    (trueFalseImpossible (trans (sym maskTrue) maskFalse))

basisAtBoundary1Zero :
  ∀ plaquette target coordinate →
  Boundary.plaquetteBoundaryMask plaquette target ≡ false →
  Basis.physicalBasis target
    (pair coordinate (Boundary.boundaryCell1 plaquette))
  ≡ 0ℚ
basisAtBoundary1Zero plaquette target coordinate maskFalse
  with Calibration.physicalCoordinateDecidableEquality
    (pair coordinate (Boundary.boundaryCell1 plaquette)) target
... | no _ = refl
... | yes exact =
  let
    targetCellExact :
      Boundary.physicalCoordinateCell target
      ≡ Boundary.boundaryCell1 plaquette
    targetCellExact = sym (cong Boundary.physicalCoordinateCell exact)
    maskTrue =
      Boundary.plaquetteBoundaryMaskAt1
        plaquette target targetCellExact
  in
  Boundary.emptyElim
    (trueFalseImpossible (trans (sym maskTrue) maskFalse))

basisAtBoundary2Zero :
  ∀ plaquette target coordinate →
  Boundary.plaquetteBoundaryMask plaquette target ≡ false →
  Basis.physicalBasis target
    (pair coordinate (Boundary.boundaryCell2 plaquette))
  ≡ 0ℚ
basisAtBoundary2Zero plaquette target coordinate maskFalse
  with Calibration.physicalCoordinateDecidableEquality
    (pair coordinate (Boundary.boundaryCell2 plaquette)) target
... | no _ = refl
... | yes exact =
  let
    targetCellExact :
      Boundary.physicalCoordinateCell target
      ≡ Boundary.boundaryCell2 plaquette
    targetCellExact = sym (cong Boundary.physicalCoordinateCell exact)
    maskTrue =
      Boundary.plaquetteBoundaryMaskAt2
        plaquette target targetCellExact
  in
  Boundary.emptyElim
    (trueFalseImpossible (trans (sym maskTrue) maskFalse))

basisAtBoundary3Zero :
  ∀ plaquette target coordinate →
  Boundary.plaquetteBoundaryMask plaquette target ≡ false →
  Basis.physicalBasis target
    (pair coordinate (Boundary.boundaryCell3 plaquette))
  ≡ 0ℚ
basisAtBoundary3Zero plaquette target coordinate maskFalse
  with Calibration.physicalCoordinateDecidableEquality
    (pair coordinate (Boundary.boundaryCell3 plaquette)) target
... | no _ = refl
... | yes exact =
  let
    targetCellExact :
      Boundary.physicalCoordinateCell target
      ≡ Boundary.boundaryCell3 plaquette
    targetCellExact = sym (cong Boundary.physicalCoordinateCell exact)
    maskTrue =
      Boundary.plaquetteBoundaryMaskAt3
        plaquette target targetCellExact
  in
  Boundary.emptyElim
    (trueFalseImpossible (trans (sym maskTrue) maskFalse))

------------------------------------------------------------------------
-- Therefore all four physical tangent insertions vanish outside the mask.
------------------------------------------------------------------------

basisInsertion0Zero :
  ∀ site axes target →
  Boundary.plaquetteBoundaryMask (pair site axes) target ≡ false →
  Plaquette.insertionAt
    (Physical.decodePhysicalSU2 (Basis.physicalBasis target))
    (Plaquette.pairLeft axes) site
  ≡ Wilson.vec3 0ℚ 0ℚ 0ℚ
basisInsertion0Zero site axes target maskFalse
  rewrite basisAtBoundary0Zero (pair site axes) target Physical.coordinateX maskFalse
        | basisAtBoundary0Zero (pair site axes) target Physical.coordinateY maskFalse
        | basisAtBoundary0Zero (pair site axes) target Physical.coordinateZ maskFalse = refl

basisInsertion1Zero :
  ∀ site axes target →
  Boundary.plaquetteBoundaryMask (pair site axes) target ≡ false →
  Plaquette.insertionAt
    (Physical.decodePhysicalSU2 (Basis.physicalBasis target))
    (Plaquette.pairRight axes)
    (Plaquette.Hodge4.shiftForward (Plaquette.pairLeft axes) site)
  ≡ Wilson.vec3 0ℚ 0ℚ 0ℚ
basisInsertion1Zero site axes target maskFalse
  rewrite basisAtBoundary1Zero (pair site axes) target Physical.coordinateX maskFalse
        | basisAtBoundary1Zero (pair site axes) target Physical.coordinateY maskFalse
        | basisAtBoundary1Zero (pair site axes) target Physical.coordinateZ maskFalse = refl

basisInsertion2Zero :
  ∀ site axes target →
  Boundary.plaquetteBoundaryMask (pair site axes) target ≡ false →
  Plaquette.insertionAt
    (Physical.decodePhysicalSU2 (Basis.physicalBasis target))
    (Plaquette.pairLeft axes)
    (Plaquette.Hodge4.shiftForward (Plaquette.pairRight axes) site)
  ≡ Wilson.vec3 0ℚ 0ℚ 0ℚ
basisInsertion2Zero site axes target maskFalse
  rewrite basisAtBoundary2Zero (pair site axes) target Physical.coordinateX maskFalse
        | basisAtBoundary2Zero (pair site axes) target Physical.coordinateY maskFalse
        | basisAtBoundary2Zero (pair site axes) target Physical.coordinateZ maskFalse = refl

basisInsertion3Zero :
  ∀ site axes target →
  Boundary.plaquetteBoundaryMask (pair site axes) target ≡ false →
  Plaquette.insertionAt
    (Physical.decodePhysicalSU2 (Basis.physicalBasis target))
    (Plaquette.pairRight axes) site
  ≡ Wilson.vec3 0ℚ 0ℚ 0ℚ
basisInsertion3Zero site axes target maskFalse
  rewrite basisAtBoundary3Zero (pair site axes) target Physical.coordinateX maskFalse
        | basisAtBoundary3Zero (pair site axes) target Physical.coordinateY maskFalse
        | basisAtBoundary3Zero (pair site axes) target Physical.coordinateZ maskFalse = refl

positiveLinkJetFirstZero :
  ∀ background field site axis →
  Plaquette.insertionAt field axis site ≡ Wilson.vec3 0ℚ 0ℚ 0ℚ →
  Wilson.factorFirst
    (Plaquette.positiveLinkJet background field site axis)
  ≡ Wilson.zeroQ
positiveLinkJetFirstZero background field site axis insertionZero =
  trans
    (cong
      (λ selected →
        Plaquette.link background (pair site axis)
          Wilson.*q Wilson.pureQuaternion selected)
      insertionZero)
    (Wilson.quaternionMultiplyZeroRight
      (Plaquette.link background (pair site axis)))

inverseLinkJetFirstZero :
  ∀ background field site axis →
  Plaquette.insertionAt field axis site ≡ Wilson.vec3 0ℚ 0ℚ 0ℚ →
  Wilson.factorFirst
    (Plaquette.inverseLinkJet background field site axis)
  ≡ Wilson.zeroQ
inverseLinkJetFirstZero background field site axis insertionZero =
  let
    inverse = Plaquette.inverseLink background (pair site axis)
  in
  trans
    (cong
      (λ selected →
        Wilson.negQ (Wilson.pureQuaternion selected) Wilson.*q inverse)
      insertionZero)
    (trans
      (cong (Wilson._*q inverse) negPureZero)
      (quaternionMultiplyZeroLeft inverse))

------------------------------------------------------------------------
-- Actual physical Wilson first-variation coordinate and support theorem.
------------------------------------------------------------------------

plaquetteFirstVariationCovector :
  Plaquette.RationalSU2Background4 → Plaquette.Plaquette4 → KKT.StateVector
plaquetteFirstVariationCovector background plaquette coordinate =
  First.wilsonFirstVariationNumerator
    (Plaquette.plaquetteFactorJets background
      (Physical.decodePhysicalSU2 (Basis.physicalBasis coordinate))
      plaquette)

plaquetteBasisFirstProductZero :
  ∀ background site axes coordinate →
  Boundary.plaquetteBoundaryMask (pair site axes) coordinate ≡ false →
  Wilson.orderedFirstProduct
    (Plaquette.plaquetteFactorJets background
      (Physical.decodePhysicalSU2 (Basis.physicalBasis coordinate))
      (pair site axes))
  ≡ Wilson.zeroQ
plaquetteBasisFirstProductZero background site axes coordinate maskFalse =
  let
    field = Physical.decodePhysicalSU2 (Basis.physicalBasis coordinate)

    first0 = positiveLinkJetFirstZero background field
      site (Plaquette.pairLeft axes)
      (basisInsertion0Zero site axes coordinate maskFalse)

    first1 = positiveLinkJetFirstZero background field
      (Plaquette.Hodge4.shiftForward (Plaquette.pairLeft axes) site)
      (Plaquette.pairRight axes)
      (basisInsertion1Zero site axes coordinate maskFalse)

    first2 = inverseLinkJetFirstZero background field
      (Plaquette.Hodge4.shiftForward (Plaquette.pairRight axes) site)
      (Plaquette.pairLeft axes)
      (basisInsertion2Zero site axes coordinate maskFalse)

    first3 = inverseLinkJetFirstZero background field
      site (Plaquette.pairRight axes)
      (basisInsertion3Zero site axes coordinate maskFalse)
  in
  orderedFirstProductAllFirstZero
    (Plaquette.plaquetteFactorJets background field (pair site axes))
    (first0 , (first1 , (first2 , (first3 , tt))))

plaquetteFirstVariationOutsideBoundaryZero :
  ∀ background site axes coordinate →
  Boundary.plaquetteBoundaryMask (pair site axes) coordinate ≡ false →
  plaquetteFirstVariationCovector background (pair site axes) coordinate
  ≡ 0ℚ
plaquetteFirstVariationOutsideBoundaryZero
    background site axes coordinate maskFalse =
  trans
    (cong (λ selected → - Wilson.q0 selected)
      (plaquetteBasisFirstProductZero
        background site axes coordinate maskFalse))
    (ℚRing.solve [])

plaquetteFirstVariationSupported :
  ∀ background plaquette →
  SubsetSource.PlaquetteSupportedSource plaquette
    (plaquetteFirstVariationCovector background plaquette)
plaquetteFirstVariationSupported background (pair site axes) = record
  { SubsetSource.PlaquetteSupportedSource.support = record
      { Projector.PhysicalConstraintProjectorImage.outsideMaskZero =
          λ coordinate maskFalse →
            plaquetteFirstVariationOutsideBoundaryZero
              background site axes coordinate maskFalse
      }
  }

literalWilsonSourceDefectSubsetProducer :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    background bondField plaquette →
  SubsetSource.LiteralSourceDefectSubsetProducer
    pseudoData
    (plaquetteFirstVariationCovector background plaquette)
    bondField plaquette
literalWilsonSourceDefectSubsetProducer pseudoData background bondField plaquette =
  record
    { SubsetSource.LiteralSourceDefectSubsetProducer.sourceSupported =
        plaquetteFirstVariationSupported background plaquette
    }

selectedPhysicalFirstVariationPlaquetteSupportLevel : ProofLevel
selectedPhysicalFirstVariationPlaquetteSupportLevel = machineChecked

literalWilsonSourceDefectSubsetProducerLevel : ProofLevel
literalWilsonSourceDefectSubsetProducerLevel = machineChecked
