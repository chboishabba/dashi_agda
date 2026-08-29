module DASHI.Physics.Closure.NSTriadKNThreeClassPositiveResidualCompilerRound215Exact where

------------------------------------------------------------------------
-- ROUND215 / BACKWARD BIDI COMPILER FOR ALL THREE PHYSICAL BONY CLASSES
--
-- Round185 used the sufficient but unnecessarily strong condition that each
-- within-class Gram debt be nonpositive. Round202 later corrected the global
-- contract: positive covariance is admissible when quantitatively bounded.
--
-- This module combines that corrected contract with Round184's universal
-- three-class factor.  For a physical three-class signed fibre, it is enough to
-- prove
--
--   D_FL <= R_FL,  D_HH <= R_HH,  D_CC <= R_CC.
--
-- Then
--
--   ||S_FL + S_HH + S_CC||^2
--     <= 3 * ((M_FL+R_FL) + (M_HH+R_HH) + (M_CC+R_CC)).
--
-- Therefore the backward consumer for Package A has no hidden sign theorem:
-- the only remaining classwise mathematics is construction of three physical,
-- cutoff-uniform quartic residual budgets.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNThreeClassFibreQuadraticRound184Exact as R184
import DASHI.Physics.Closure.NSTriadKNClasswisePartnerGramPaymentRound185Exact as R185
import DASHI.Physics.Closure.NSTriadKNRawCurlLowOutputKernelMassRound178Exact as R178

record ThreeClassPositiveResidualPayment (fibre : R185.ThreeClassSignedFibre) : Set where
  constructor three-class-positive-residual-payment
  field
    farLowResidual highHighResidual comparableResidual : ℚ
    farLowDebtBound :
      R180.gramDebt (R185.farLowCells fibre) ≤ farLowResidual
    highHighDebtBound :
      R180.gramDebt (R185.highHighCells fibre) ≤ highHighResidual
    comparableDebtBound :
      R180.gramDebt (R185.comparableCells fibre) ≤ comparableResidual

open ThreeClassPositiveResidualPayment public

classBound :
  (cells : _) → (residual : ℚ) →
  R180.gramDebt cells ≤ residual →
  L2.complex3NormSquared (R180.sumCells cells)
  ≤ R180.cellMassSum cells + residual
classBound cells residual debtBound =
  subst
    (λ left → left ≤ R180.cellMassSum cells + residual)
    (R180.gramLedger cells)
    (ℚP.+-monoʳ-≤ (R180.cellMassSum cells) debtBound)

threeClassPositiveResidualClosesGlobalFibre :
  (fibre : R185.ThreeClassSignedFibre) →
  (payment : ThreeClassPositiveResidualPayment fibre) →
  L2.complex3NormSquared (R185.globalThreeClassSum fibre)
  ≤ R178.three *
      ( (R180.cellMassSum (R185.farLowCells fibre) + farLowResidual payment)
      + (R180.cellMassSum (R185.highHighCells fibre) + highHighResidual payment)
      + (R180.cellMassSum (R185.comparableCells fibre) + comparableResidual payment))
threeClassPositiveResidualClosesGlobalFibre fibre payment =
  R184.threeClassPaidQuadraticBound
    (R185.farLowSum fibre)
    (R185.highHighSum fibre)
    (R185.comparableSum fibre)
    (R180.cellMassSum (R185.farLowCells fibre) + farLowResidual payment)
    (R180.cellMassSum (R185.highHighCells fibre) + highHighResidual payment)
    (R180.cellMassSum (R185.comparableCells fibre) + comparableResidual payment)
    (classBound (R185.farLowCells fibre) (farLowResidual payment)
      (farLowDebtBound payment))
    (classBound (R185.highHighCells fibre) (highHighResidual payment)
      (highHighDebtBound payment))
    (classBound (R185.comparableCells fibre) (comparableResidual payment)
      (comparableDebtBound payment))

round215ThreeClassPositiveResidualCompilerClosed : Bool
round215ThreeClassPositiveResidualCompilerClosed = true

round215RequiresWithinClassGramNegativity : Bool
round215RequiresWithinClassGramNegativity = false

round215FarLowPhysicalResidualConstructed : Bool
round215FarLowPhysicalResidualConstructed = false

round215HighHighPhysicalResidualConstructed : Bool
round215HighHighPhysicalResidualConstructed = false

round215ComparablePhysicalResidualConstructed : Bool
round215ComparablePhysicalResidualConstructed = false

round215PackageAClosed : Bool
round215PackageAClosed = false

round215ClayPromotion : Bool
round215ClayPromotion = false

round215ThreeClassPositiveResidualCompilerClosedIsTrue :
  round215ThreeClassPositiveResidualCompilerClosed ≡ true
round215ThreeClassPositiveResidualCompilerClosedIsTrue = refl

round215RequiresWithinClassGramNegativityIsFalse :
  round215RequiresWithinClassGramNegativity ≡ false
round215RequiresWithinClassGramNegativityIsFalse = refl
