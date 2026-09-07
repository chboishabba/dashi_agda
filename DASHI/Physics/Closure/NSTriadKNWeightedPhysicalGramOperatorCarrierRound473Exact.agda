module DASHI.Physics.Closure.NSTriadKNWeightedPhysicalGramOperatorCarrierRound473Exact where

------------------------------------------------------------------------
-- ROUND473 / LITERAL R180/R383 SIGNED GRAM AS AN OPERATOR QUADRATIC FORM
--
-- The new Lean consumer is an l2->l2 bound on the fixed-output Gram quadratic
-- form for arbitrary coefficients.  The Agda repository already owns the exact
-- signed Gram matrix implicitly:
--
--   R383.pairGram u v = 2 Re <u,v>
--   R383.allPairSum cells = R180.gramDebt cells.
--
-- This owner adds only the missing coefficient sequence.  Rational coefficients
-- are inserted into the literal Complex3 cells, so
--
--   Q(c) = R383.allPairSum (c_i G_i)
--   M(c) = R180.cellMassSum (c_i G_i)
--
-- is the same physical signed Gram carrier, not an abstract surrogate.  R180's
-- exact polarization ledger then turns an R471 GramOperatorBound into a bound
-- for every weighted finite fibre.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNGramDebtPairExpansionRound383Exact as R383
import DASHI.Physics.Closure.NSTriadKNGramOperatorBoundConsumerRound471Exact as R471

F : C3.RealField _
F = Rational.rationalRealField

weightedCells :
  List ℚ → List (C3.Complex3 F) → List (C3.Complex3 F)
weightedCells [] cells = []
weightedCells coefficients [] = []
weightedCells (coefficient ∷ coefficients) (cell ∷ cells) =
  C3.complex3Scale (C3.realEmbed F coefficient) cell
    ∷ weightedCells coefficients cells

weightedSignedGram :
  List (C3.Complex3 F) → List ℚ → ℚ
weightedSignedGram cells coefficients =
  R383.allPairSum (weightedCells coefficients cells)

weightedCellMass :
  List (C3.Complex3 F) → List ℚ → ℚ
weightedCellMass cells coefficients =
  R180.cellMassSum (weightedCells coefficients cells)

weightedCellSum :
  List (C3.Complex3 F) → List ℚ → C3.Complex3 F
weightedCellSum cells coefficients =
  R180.sumCells (weightedCells coefficients cells)

PhysicalSignedGramOperatorBound :
  List (C3.Complex3 F) → ℚ → Set
PhysicalSignedGramOperatorBound cells A =
  R471.GramOperatorBound
    (List ℚ)
    (weightedSignedGram cells)
    (weightedCellMass cells)
    A

weightedPhysicalGramLedger :
  (cells : List (C3.Complex3 F)) →
  (coefficients : List ℚ) →
  L2.complex3NormSquared (weightedCellSum cells coefficients)
  ≡ weightedCellMass cells coefficients
      + weightedSignedGram cells coefficients
weightedPhysicalGramLedger cells coefficients =
  let weighted = weightedCells coefficients cells in
  trans
    (R180.finiteFibreGramLedger weighted)
    (cong
      (R180.cellMassSum weighted +_)
      (R383.r180GramDebtIsAllPairSum weighted))

weightedPhysicalFibreBoundFromGramOperator :
  (cells : List (C3.Complex3 F)) →
  (A : ℚ) →
  PhysicalSignedGramOperatorBound cells A →
  (coefficients : List ℚ) →
  L2.complex3NormSquared (weightedCellSum cells coefficients)
  ≤ (1ℚ + A) * weightedCellMass cells coefficients
weightedPhysicalFibreBoundFromGramOperator cells A B coefficients =
  let
    mass = weightedCellMass cells coefficients
    gram = weightedSignedGram cells coefficients

    gramPaid : gram ≤ A * mass
    gramPaid = R471.quadraticBound B coefficients

    added : mass + gram ≤ mass + A * mass
    added = ℚP.+-mono-≤ ℚP.≤-refl gramPaid

    endpoint : mass + A * mass ≡ (1ℚ + A) * mass
    endpoint = solve (A ∷ mass ∷ [])
  in
  subst
    (λ lower → lower ≤ (1ℚ + A) * mass)
    (weightedPhysicalGramLedger cells coefficients)
    (subst
      ((mass + gram) ≤_)
      endpoint
      added)

round473LiteralR383SignedPairFormUsed : Bool
round473LiteralR383SignedPairFormUsed = true

round473ArbitraryCoefficientSequenceInstalled : Bool
round473ArbitraryCoefficientSequenceInstalled = true

round473GramBoundToWeightedFibreCompilerClosed : Bool
round473GramBoundToWeightedFibreCompilerClosed = true

round473AbsoluteValueInsertedIntoGram : Bool
round473AbsoluteValueInsertedIntoGram = false

round473PhysicalUniformGramBoundClosed : Bool
round473PhysicalUniformGramBoundClosed = false

round473PackageAClosed : Bool
round473PackageAClosed = false

round473ClayPromotion : Bool
round473ClayPromotion = false

round473AbsoluteValueInsertedIntoGramIsFalse :
  round473AbsoluteValueInsertedIntoGram ≡ false
round473AbsoluteValueInsertedIntoGramIsFalse = refl

round473PhysicalUniformGramBoundClosedIsFalse :
  round473PhysicalUniformGramBoundClosed ≡ false
round473PhysicalUniformGramBoundClosedIsFalse = refl
