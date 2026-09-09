module DASHI.Physics.Closure.NSTriadKNCauchyResolvedPositiveCellCarrierRound482Exact where

------------------------------------------------------------------------
-- ROUND482 / R446 POSITIVE-RATE CELLS -> LITERAL R477 RESOLVED FAMILY
--
-- R481 says the first missing NS obligation is the R480 same-object snapshot.
-- The shortest representation route is NOT to index R477 by every raw physical
-- triad and then prove positivity away from the selected fibre.  R447 already
-- constructs a list of R446.PositiveRateComplex3Cell values.  That record
-- carries strict rate positivity at the type level.
--
-- Therefore we instantiate R477 directly on PositiveRateComplex3Cell:
--
--   indices          = the selected R447 physicalCells list
--   cell             = R446.value
--   rate             = R446.rate
--   resolventWeight  = R446.cauchyKernel
--
-- Cauchy symmetry and the division-free inverse law are then inherited from
-- R443 for EVERY index without another physical theorem.
--
-- The selected physical coefficient is the constant 1.  At that coefficient,
-- every R477 resolved atom is definitionally/ring-equal to the literal R446
-- Hermitian Cauchy pair term.  The only remaining same-object algebra is the
-- finite summation convention: R477 uses the ordered full double sum, whereas
-- R446 writes diagonal + twice the upper-triangle row sum.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNRationalCauchySchurComplementRound443Exact as R443
import DASHI.Physics.Closure.NSTriadKNRationalComplex3CauchyPSDRound446Exact as R446
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedGramOperatorRound477Exact as R477

PositiveCell : Set
PositiveCell = R446.PositiveRateComplex3Cell

positiveCellResolvedFamily : List PositiveCell → R477.CauchyResolvedCellFamily PositiveCell
positiveCellResolvedFamily cells = record
  { R477.indices = cells
  ; R477.cell = R446.value
  ; R477.rate = R446.rate
  ; R477.resolventWeight = R446.cauchyKernel
  ; R477.resolventSymmetric = λ left right →
      R443.cauchyEntrySymmetric (R446.rate left) (R446.rate right)
  ; R477.resolventLaw = λ left right →
      R443.cauchyEntryInverseLaw
        (R446.rate left) (R446.rate right)
        (R446.ratePositive left) (R446.ratePositive right)
  }

selectedCoefficient : PositiveCell → ℚ
selectedCoefficient cell = 1ℚ

resolvedAtomAtSelectedCoefficient :
  (cells : List PositiveCell) →
  (left right : PositiveCell) →
  R477.resolvedAtom
    (positiveCellResolvedFamily cells)
    selectedCoefficient left right
  ≡ R446.cauchyKernel left right
      * R179.realHermitianCross (R446.value left) (R446.value right)
resolvedAtomAtSelectedCoefficient cells left right =
  solve
    ( R446.cauchyKernel left right
    ∷ R179.realHermitianCross (R446.value left) (R446.value right)
    ∷ [])

resolvedRowAtSelectedCoefficient :
  (cells : List PositiveCell) →
  (head : PositiveCell) →
  (rest : List PositiveCell) →
  R477.resolvedRow
    (positiveCellResolvedFamily cells)
    selectedCoefficient head rest
  ≡ R446.hermitianRow head rest
resolvedRowAtSelectedCoefficient cells head [] = refl
resolvedRowAtSelectedCoefficient cells head (cell ∷ rest) =
  cong₂ _+_
    (resolvedAtomAtSelectedCoefficient cells head cell)
    (resolvedRowAtSelectedCoefficient cells head rest)

------------------------------------------------------------------------
-- Ordered full form: exact intermediate carrier between R477 and R446.
------------------------------------------------------------------------

orderedHermitianRows : List PositiveCell → List PositiveCell → ℚ
orderedHermitianRows all [] = 0ℚ
orderedHermitianRows all (head ∷ rest) =
  R446.hermitianRow head all + orderedHermitianRows all rest

resolvedQuadraticFromAtSelectedCoefficient :
  (cells : List PositiveCell) →
  (items : List PositiveCell) →
  R477.resolvedQuadraticFrom
    (positiveCellResolvedFamily cells)
    selectedCoefficient items
  ≡ orderedHermitianRows cells items
resolvedQuadraticFromAtSelectedCoefficient cells [] = refl
resolvedQuadraticFromAtSelectedCoefficient cells (head ∷ rest) =
  cong₂ _+_
    (resolvedRowAtSelectedCoefficient cells head cells)
    (resolvedQuadraticFromAtSelectedCoefficient cells rest)

resolvedQuadraticAtSelectedCoefficientIsOrderedHermitianRows :
  (cells : List PositiveCell) →
  R477.resolvedQuadratic
    (positiveCellResolvedFamily cells)
    selectedCoefficient
  ≡ orderedHermitianRows cells cells
resolvedQuadraticAtSelectedCoefficientIsOrderedHermitianRows cells =
  resolvedQuadraticFromAtSelectedCoefficient cells cells

------------------------------------------------------------------------
-- Search boundary.
------------------------------------------------------------------------

round482PositiveCellResolvedFamilyConstructed : Bool
round482PositiveCellResolvedFamilyConstructed = true

round482CauchySymmetryReceiptInherited : Bool
round482CauchySymmetryReceiptInherited = true

round482DivisionFreeResolventLawInherited : Bool
round482DivisionFreeResolventLawInherited = true

round482SelectedCoefficientIsConstantOne : Bool
round482SelectedCoefficientIsConstantOne = true

round482SelectedResolvedAtomsMatchR446PairTerms : Bool
round482SelectedResolvedAtomsMatchR446PairTerms = true

round482SelectedResolvedRowsMatchR446HermitianRows : Bool
round482SelectedResolvedRowsMatchR446HermitianRows = true

round482SelectedResolvedQuadraticMatchesOrderedFullRows : Bool
round482SelectedResolvedQuadraticMatchesOrderedFullRows = true

round482OrderedFullRowsMatchR446HermitianCauchyForm : Bool
round482OrderedFullRowsMatchR446HermitianCauchyForm = false

round482R480SnapshotWeldClosed : Bool
round482R480SnapshotWeldClosed = false

round482ClayPromotion : Bool
round482ClayPromotion = false

round482OrderedFullRowsMatchR446HermitianCauchyFormIsFalse :
  round482OrderedFullRowsMatchR446HermitianCauchyForm ≡ false
round482OrderedFullRowsMatchR446HermitianCauchyFormIsFalse = refl

round482R480SnapshotWeldClosedIsFalse :
  round482R480SnapshotWeldClosed ≡ false
round482R480SnapshotWeldClosedIsFalse = refl
