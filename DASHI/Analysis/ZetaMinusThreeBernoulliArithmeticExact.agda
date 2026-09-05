module DASHI.Analysis.ZetaMinusThreeBernoulliArithmeticExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; -_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

------------------------------------------------------------------------
-- ZETA(-3) NUMERICAL COMPILER
--
-- The analytic theorem is the classical Bernoulli special-value relation
--   zeta(1-n) = -B_n/n.
-- This module does NOT prove that analytic-continuation theorem.  It proves only
-- the exact rational consequence for n=4 once B4 = -1/30 has been supplied.
------------------------------------------------------------------------

bernoulliB4 : ℚ
bernoulliB4 = - (+ 1 / 30)

oneQuarter : ℚ
oneQuarter = + 1 / 4

oneOver120 : ℚ
oneOver120 = + 1 / 120

minusB4OverFour : ℚ
minusB4OverFour = (- bernoulliB4) * oneQuarter

bernoulliB4CompilerProducesOneOver120 :
  minusB4OverFour ≡ oneOver120
bernoulliB4CompilerProducesOneOver120 = ℚRing.solve []

record ZetaMinusThreeBernoulliAnalyticReceipt : Set₁ where
  field
    ZetaValue : Set
    zetaMinusThree : ZetaValue

    BernoulliValue : Set
    B4 : BernoulliValue

    analyticContinuationAtMinusThree : Set
    bernoulliSpecialValueFormulaAtFour : Set
    bernoulliB4IdentifiedWithMinusOneOver30 : Set
    zetaValueTransportToRational : Set

open ZetaMinusThreeBernoulliAnalyticReceipt public

record ZetaMinusThreeCompilerStatus : Set where
  field
    bernoulliRationalArithmeticOwned : Bool
    analyticContinuationFormulaClosed : Bool
    sameObjectZetaTransportClosed : Bool

    bernoulliRationalArithmeticOwnedIsTrue :
      bernoulliRationalArithmeticOwned ≡ true
    analyticContinuationFormulaClosedIsFalse :
      analyticContinuationFormulaClosed ≡ false
    sameObjectZetaTransportClosedIsFalse :
      sameObjectZetaTransportClosed ≡ false

open ZetaMinusThreeCompilerStatus public

canonicalZetaMinusThreeCompilerStatus : ZetaMinusThreeCompilerStatus
canonicalZetaMinusThreeCompilerStatus = record
  { bernoulliRationalArithmeticOwned = true
  ; analyticContinuationFormulaClosed = false
  ; sameObjectZetaTransportClosed = false
  ; bernoulliRationalArithmeticOwnedIsTrue = refl
  ; analyticContinuationFormulaClosedIsFalse = refl
  ; sameObjectZetaTransportClosedIsFalse = refl
  }
