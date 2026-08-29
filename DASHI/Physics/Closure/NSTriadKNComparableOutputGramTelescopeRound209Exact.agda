module DASHI.Physics.Closure.NSTriadKNComparableOutputGramTelescopeRound209Exact where

------------------------------------------------------------------------
-- ROUND209 / OUTPUTWISE LAW OF TOTAL GRAM FOR COMPARABLE PARTNERS
--
-- Round207 restricts Gram covariance to one Fourier output.  Round208 restores
-- the physical outer Fourier L2 carrier by summing squared output-block norms.
-- This file telescopes the exact same-output Gram identity over the finite list
-- of outputs:
--
--   sum_k ||S_CC(k)||^2
--     = sum_k cellMass_CC(k) + sum_k debt_CC(k).
--
-- There is deliberately NO cross-output Gram debt.  The sole CC analytic
-- target is the sum of SAME-OUTPUT between-partner debts.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlPartnerMassRound187Exact as R187
import DASHI.Physics.Closure.NSTriadKNComparableFixedOutputCarrierRound207Exact as R207
import DASHI.Physics.Closure.NSTriadKNComparableOutputL2CarrierRound208Exact as R208

F = R187.F

outputCellMassSum :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I} →
  (family : R208.ComparableOutputBlockFamily system) →
  List Z3.FourierMode → ℚ
outputCellMassSum family [] = 0ℚ
outputCellMassSum family (output ∷ rest) =
  R180.cellMassSum
    (R207.fixedOutputPartnerCells (R208.partnersAt family output))
  + outputCellMassSum family rest

outputSameModeDebtSum :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I} →
  (family : R208.ComparableOutputBlockFamily system) →
  List Z3.FourierMode → ℚ
outputSameModeDebtSum family [] = 0ℚ
outputSameModeDebtSum family (output ∷ rest) =
  R207.fixedOutputBetweenPartnerDebt (R208.partnersAt family output)
  + outputSameModeDebtSum family rest

outputwiseComparableGramTelescope :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    (family : R208.ComparableOutputBlockFamily system)
    (outs : List Z3.FourierMode) →
  R208.outputBlockMassSum family outs
  ≡ outputCellMassSum family outs + outputSameModeDebtSum family outs
outputwiseComparableGramTelescope family [] = refl
outputwiseComparableGramTelescope family (output ∷ rest)
  rewrite R207.fixedOutputCompressedGramLedger (R208.partnersAt family output)
        | outputwiseComparableGramTelescope family rest =
  solve
    ( R180.cellMassSum
        (R207.fixedOutputPartnerCells (R208.partnersAt family output))
    ∷ R207.fixedOutputBetweenPartnerDebt (R208.partnersAt family output)
    ∷ outputCellMassSum family rest
    ∷ outputSameModeDebtSum family rest
    ∷ [])

comparableOuterL2GramTelescope :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    (family : R208.ComparableOutputBlockFamily system) →
  R208.comparableOuterL2Mass family
  ≡ outputCellMassSum family (R208.outputs family)
    + outputSameModeDebtSum family (R208.outputs family)
comparableOuterL2GramTelescope family =
  outputwiseComparableGramTelescope family (R208.outputs family)

round209CrossOutputCovarianceEliminatedByCarrier : Bool
round209CrossOutputCovarianceEliminatedByCarrier = true

round209OnlySameOutputComparableDebtRemains : Bool
round209OnlySameOutputComparableDebtRemains = true

round209SameOutputComparableDebtQuantitativelyPaid : Bool
round209SameOutputComparableDebtQuantitativelyPaid = false

round209PhysicalCCResidualBudgetClosed : Bool
round209PhysicalCCResidualBudgetClosed = false

round209PackageAClosed : Bool
round209PackageAClosed = false

round209ClayPromotion : Bool
round209ClayPromotion = false

round209CrossOutputCovarianceEliminatedByCarrierIsTrue :
  round209CrossOutputCovarianceEliminatedByCarrier ≡ true
round209CrossOutputCovarianceEliminatedByCarrierIsTrue = refl

round209SameOutputComparableDebtQuantitativelyPaidIsFalse :
  round209SameOutputComparableDebtQuantitativelyPaid ≡ false
round209SameOutputComparableDebtQuantitativelyPaidIsFalse = refl
