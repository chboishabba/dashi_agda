module DASHI.Physics.Closure.NSTriadKNFourSignInnerFibreGramBoundaryRound577Exact where

------------------------------------------------------------------------
-- ROUND577 / EXACT VARIABLE-FIBRE GRAM BOUNDARY AFTER R576
--
-- R576 closes the fixed four-helicity recombination for every inner incidence:
--
--   ||M_tau||^2 <= 36 |k_tau|^2 E_p E_q.
--
-- The remaining danger is NOT another local norm estimate.  It is the signed
-- covariance created when a variable number of distinct incidences on the same
-- output fibre are summed.  R180 already owns the exact finite identity
--
--   ||sum cells||^2 = sum ||cell||^2 + GramDebt(cells).
--
-- This owner welds that old ledger to the NEW literal R571/R572 four-sign cell.
-- It also sums R576's pointwise majorants over an arbitrary finite incidence
-- list.  Therefore the complete variable-fibre problem is now exactly:
--
--   pay one signed Gram residual for the actual fourSignInner cells.
--
-- Nonpositivity is NOT required: any quantitative residual upper bound is
-- sufficient.  This mirrors the later R215 correction and avoids reinstating
-- the obsolete 'all covariance must cancel' requirement.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNFourHelicityVectorRecombinationRound576Exact as R576
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalFibre
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module Cell = R576.PhysicalRecombination
    E I O system S L velocityTransverse

  fourSignCells :
    List Physical.PhysicalTriadIncidence → List (C3.Complex3 F)
  fourSignCells items = map Cell.fourSignInner items

  foldIsGramSum :
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector Cell.fourSignInner items
    ≡ R180.sumCells (fourSignCells items)
  foldIsGramSum [] = refl
  foldIsGramSum (tau ∷ rest) =
    cong₂ C3.complex3Add refl (foldIsGramSum rest)

  exactFourSignFibreGramLedger :
    (items : List Physical.PhysicalTriadIncidence) →
    L2.complex3NormSquared (R224.foldVector Cell.fourSignInner items)
    ≡ R180.cellMassSum (fourSignCells items)
      + R180.gramDebt (fourSignCells items)
  exactFourSignFibreGramLedger items =
    trans
      (cong L2.complex3NormSquared (foldIsGramSum items))
      (R180.finiteFibreGramLedger (fourSignCells items))

  pointwiseMajorant : Physical.PhysicalTriadIncidence → ℚ
  pointwiseMajorant tau =
    R576.thirtySix * C3.normSquared I (Physical.k tau)
      * L2.complex3NormSquared (Audit.velocity system (Physical.p tau))
      * L2.complex3NormSquared (Audit.velocity system (Physical.q tau))

  majorantSum : List Physical.PhysicalTriadIncidence → ℚ
  majorantSum [] = 0ℚ
  majorantSum (tau ∷ rest) = pointwiseMajorant tau + majorantSum rest

  cellMassSumBound :
    (items : List Physical.PhysicalTriadIncidence) →
    ((tau : Physical.PhysicalTriadIncidence) →
      Z3.NonZeroMode (Physical.k tau)) →
    R180.cellMassSum (fourSignCells items) ≤ majorantSum items
  cellMassSumBound [] allNonzero = ℚP.≤-refl
  cellMassSumBound (tau ∷ rest) allNonzero =
    ℚP.+-mono-≤
      (Cell.fourSignInnerLowOutputBound tau (allNonzero tau))
      (cellMassSumBound rest allNonzero)

  record QuantitativeFourSignGramPayment577
      (items : List Physical.PhysicalTriadIncidence) : Set where
    constructor quantitative-four-sign-gram-payment-577
    field
      gramResidual577 : ℚ
      gramDebtUpper577 :
        R180.gramDebt (fourSignCells items) ≤ gramResidual577

  open QuantitativeFourSignGramPayment577 public

  paidVariableFibreBound :
    (items : List Physical.PhysicalTriadIncidence) →
    ((tau : Physical.PhysicalTriadIncidence) →
      Z3.NonZeroMode (Physical.k tau)) →
    (payment : QuantitativeFourSignGramPayment577 items) →
    L2.complex3NormSquared (R224.foldVector Cell.fourSignInner items)
    ≤ majorantSum items + gramResidual577 payment
  paidVariableFibreBound items allNonzero payment =
    let
      ledger = exactFourSignFibreGramLedger items
      masses = cellMassSumBound items allNonzero
      debt = gramDebtUpper577 payment
      combined :
        R180.cellMassSum (fourSignCells items)
          + R180.gramDebt (fourSignCells items)
        ≤ majorantSum items + gramResidual577 payment
      combined = ℚP.+-mono-≤ masses debt
    in
    subst
      (λ lower →
        lower ≤ majorantSum items + gramResidual577 payment)
      (sym ledger)
      combined

  nonpositiveGramIsOnlySufficientNotNecessary :
    (items : List Physical.PhysicalTriadIncidence) →
    R180.gramDebt (fourSignCells items) ≤ 0ℚ →
    QuantitativeFourSignGramPayment577 items
  nonpositiveGramIsOnlySufficientNotNecessary items nonpositive =
    quantitative-four-sign-gram-payment-577 0ℚ nonpositive

------------------------------------------------------------------------
-- Status / introspective cut.
------------------------------------------------------------------------

round577R576CellBoundAttachedToExactR180GramLedger : Bool
round577R576CellBoundAttachedToExactR180GramLedger = true

round577VariableFibreCellMassMajorantSummedExactly : Bool
round577VariableFibreCellMassMajorantSummedExactly = true

round577WithinFibreGramMustBeNonpositive : Bool
round577WithinFibreGramMustBeNonpositive = false

round577QuantitativeVariableFibreGramResidualPaid : Bool
round577QuantitativeVariableFibreGramResidualPaid = false

round577VariableFibreCardinalityFactorIntroduced : Bool
round577VariableFibreCardinalityFactorIntroduced = false

round577OuterSpectatorWeightedSpacetimeBoundClosed : Bool
round577OuterSpectatorWeightedSpacetimeBoundClosed = false

round577CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round577CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round577ClayPromotion : Bool
round577ClayPromotion = false

round577R576CellBoundAttachedToExactR180GramLedgerIsTrue :
  round577R576CellBoundAttachedToExactR180GramLedger ≡ true
round577R576CellBoundAttachedToExactR180GramLedgerIsTrue = refl

round577WithinFibreGramMustBeNonpositiveIsFalse :
  round577WithinFibreGramMustBeNonpositive ≡ false
round577WithinFibreGramMustBeNonpositiveIsFalse = refl

round577ClayPromotionIsFalse : round577ClayPromotion ≡ false
round577ClayPromotionIsFalse = refl
