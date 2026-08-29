module DASHI.Physics.Closure.NSTriadKNComparableOutputResidualPaymentRound211Exact where

------------------------------------------------------------------------
-- ROUND211 / BACKWARD HALF OF THE BIDIRECTIONAL CC SEARCH
--
-- Round209 gives exactly
--
--   Q_CC = M_CC + D_CC,
--
-- where D_CC is the sum of same-output between-partner debts.  The downstream
-- Package-A consumer does not need a sign theorem, a shell count, or any more
-- internal Gram structure.  It needs one quantitative quartic majorant R_CC.
--
-- This module freezes that backward-facing socket:
--
--   D_CC <= R_CC  ==>  Q_CC <= M_CC + R_CC.
--
-- Round210 is the forward producer-side progress toward constructing such a
-- payment: every physical fixed-output CC partner now lies below the output
-- shell plus 2*Csep on both input legs.  Future analytic work should therefore
-- target this exact payment record rather than grow a parallel estimate API.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlPartnerMassRound187Exact as R187
import DASHI.Physics.Closure.NSTriadKNComparableOutputL2CarrierRound208Exact as R208
import DASHI.Physics.Closure.NSTriadKNComparableOutputGramTelescopeRound209Exact as R209
import DASHI.Physics.Closure.NSTriadKNComparableFixedOutputUpperCollarRound210Exact as R210

F = R187.F

record ComparableSameOutputResidualPayment
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    (family : R208.ComparableOutputBlockFamily system) : Set where
  constructor comparable-same-output-residual-payment
  field
    residualBudget : ℚ
    sameOutputDebtBound :
      R209.outputSameModeDebtSum family (R208.outputs family)
      ≤ residualBudget

open ComparableSameOutputResidualPayment public

comparableResidualPaymentClosesOuterMass :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    (family : R208.ComparableOutputBlockFamily system) →
  (payment : ComparableSameOutputResidualPayment family) →
  R208.comparableOuterL2Mass family
  ≤ R209.outputCellMassSum family (R208.outputs family)
      + residualBudget payment
comparableResidualPaymentClosesOuterMass family payment =
  let
    shifted :
      R209.outputCellMassSum family (R208.outputs family)
        + R209.outputSameModeDebtSum family (R208.outputs family)
      ≤ R209.outputCellMassSum family (R208.outputs family)
        + residualBudget payment
    shifted =
      ℚP.+-monoʳ-≤
        (R209.outputCellMassSum family (R208.outputs family))
        (sameOutputDebtBound payment)
  in
  subst
    (λ left →
      left ≤ R209.outputCellMassSum family (R208.outputs family)
        + residualBudget payment)
    (R209.comparableOuterL2GramTelescope family)
    shifted

round211BackwardResidualSocketExact : Bool
round211BackwardResidualSocketExact = true

round211ForwardUpperCollarAvailable : Bool
round211ForwardUpperCollarAvailable =
  R210.round210BothCCInputsUpperLocalizedToFixedOutput

round211RequiresGramNegativity : Bool
round211RequiresGramNegativity = false

round211RequiresCutoffShellCount : Bool
round211RequiresCutoffShellCount = false

round211ConcreteSameOutputResidualPaymentConstructed : Bool
round211ConcreteSameOutputResidualPaymentConstructed = false

round211PhysicalCCResidualBudgetClosed : Bool
round211PhysicalCCResidualBudgetClosed = false

round211PackageAClosed : Bool
round211PackageAClosed = false

round211ClayPromotion : Bool
round211ClayPromotion = false

round211BackwardResidualSocketExactIsTrue :
  round211BackwardResidualSocketExact ≡ true
round211BackwardResidualSocketExactIsTrue = refl

round211ForwardUpperCollarAvailableIsTrue :
  round211ForwardUpperCollarAvailable ≡ true
round211ForwardUpperCollarAvailableIsTrue = refl

round211ConcreteSameOutputResidualPaymentConstructedIsFalse :
  round211ConcreteSameOutputResidualPaymentConstructed ≡ false
round211ConcreteSameOutputResidualPaymentConstructedIsFalse = refl
