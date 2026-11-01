module DASHI.Analysis.InversePowerDerivativeCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GENERIC INVERSE-POWER DERIVATIVE COMPILER
--
-- This is theorem-shape infrastructure.  It does not define real analysis.
-- An application supplies derivative semantics on its own scalar carrier and
-- proves the inverse-power rule there.  Downstream coefficient transport is
-- then separated from the calculus receipt.
------------------------------------------------------------------------

record DerivativeStructure : Set₁ where
  field
    Scalar : Set
    Variable : Set

    Function : Set
    valueAt : Function → Variable → Scalar

    derivative : Function → Function
    DerivativeReceipt : Function → Set

    derivativeClosed : (f : Function) → DerivativeReceipt f → Set
    reading : String

open DerivativeStructure public

record InversePowerFamily (D : DerivativeStructure) : Set₁ where
  field
    coefficient : Scalar D
    inversePower : Nat → Function D
    scaledInversePower : Nat → Function D

    power3Member : Function D
    power4Member : Function D

    power3MemberLaw : power3Member ≡ scaledInversePower 3
    power4MemberLaw : power4Member ≡ scaledInversePower 4

    familyReading : String

open InversePowerFamily public

record InverseCubeDerivativeReceipt
    (D : DerivativeStructure)
    (F : InversePowerFamily D) : Set₁ where
  field
    inverseCubeDifferentiable : DerivativeReceipt D (power3Member F)

    factorThree : Set

    derivativeIsInverseFourthWithFactorThree :
      derivative D (power3Member F) ≡ power4Member F

    sameFunctionFamily : Set
    receiptReading : String

open InverseCubeDerivativeReceipt public

------------------------------------------------------------------------
-- BIDI consumer side.
------------------------------------------------------------------------

record InverseCubeDerivativeObligations
    (D : DerivativeStructure)
    (F : InversePowerFamily D) : Set₁ where
  field
    scalarCalculusAvailable : Set
    inverseCubeDifferentiable : Set
    inversePowerRuleOnSameCarrier : Set
    coefficientConstantUnderDerivative : Set
    signConventionFixed : Set

open InverseCubeDerivativeObligations public

------------------------------------------------------------------------
-- Arithmetic and calculus remain separate authority layers.
------------------------------------------------------------------------

data ArithmeticIdentityClosesDerivativePermission : Set where

arithmeticCannotAutoCloseDerivative :
  ArithmeticIdentityClosesDerivativePermission → ⊥
arithmeticCannotAutoCloseDerivative ()
