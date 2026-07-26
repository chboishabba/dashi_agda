module DASHI.Analysis.MarxDifferentialRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Analysis.MarxDifferentialCore
open import DASHI.Analysis.MarxPolynomialDifferential

------------------------------------------------------------------------
-- A one-point exact model exercises every algebraic constructor without
-- claiming that the terminal carrier is the ordinary real line.

terminalAlgebra : MarxAlgebra
terminalAlgebra =
  record
    { Carrier = ⊤
    ; zero = tt
    ; one = tt
    ; _+_ = λ _ _ → tt
    ; _-_ = λ _ _ → tt
    ; _*_ = λ _ _ → tt
    ; subSelf = λ _ → refl
    ; mulZeroRight = λ _ → refl
    ; mulOneRight = λ _ → refl
    ; mulAssoc = λ _ _ _ → refl
    ; addDifferenceFactor = λ _ _ → refl
    ; productDifferenceFactor = λ _ _ → refl
    }

terminalConstantReceipt :
  MarxFactorisation terminalAlgebra (constantFunction tt)
terminalConstantReceipt = constantFactorisation tt

terminalIdentityReceipt :
  MarxFactorisation terminalAlgebra identityFunction
terminalIdentityReceipt = identityFactorisation

terminalSumReceipt :
  MarxFactorisation terminalAlgebra
    (addFunctions identityFunction (constantFunction tt))
terminalSumReceipt =
  addFactorisations terminalIdentityReceipt terminalConstantReceipt

terminalProductReceipt :
  MarxFactorisation terminalAlgebra
    (multiplyFunctions identityFunction identityFunction)
terminalProductReceipt =
  productFactorisations terminalIdentityReceipt terminalIdentityReceipt

terminalChainReceipt :
  MarxFactorisation terminalAlgebra
    (compose identityFunction identityFunction)
terminalChainReceipt =
  chainFactorisation terminalIdentityReceipt terminalIdentityReceipt

terminalPowerTwoReceipt :
  MarxFactorisation terminalAlgebra (powerFunction (suc (suc zero)))
terminalPowerTwoReceipt = powerFactorisation (suc (suc zero))

terminalPowerNormalisation :
  PowerRuleNormalisation terminalAlgebra
terminalPowerNormalisation =
  record
    { natScale = λ _ _ → tt
    ; zeroScale = λ _ → refl
    ; successorScale = λ _ _ → refl
    ; normalisePowerDerivative = λ _ _ → refl
    }

terminalPowerRule :
  marxDerivative terminalPowerTwoReceipt tt ≡ tt
terminalPowerRule =
  powerRule terminalPowerNormalisation (suc zero) tt

terminalPolynomial : Polynomial terminalAlgebra
terminalPolynomial =
  (variable *P variable) +P constant tt

terminalPolynomialReceipt :
  MarxFactorisation terminalAlgebra (interpret terminalPolynomial)
terminalPolynomialReceipt = polynomialFactorisation terminalPolynomial

terminalRawDiagonalImpossible :
  RawDiagonalQuotient terminalAlgebra identityFunction tt →
  Agda.Builtin.Unit.⊤
terminalRawDiagonalImpossible raw =
  let impossible = rawDiagonalQuotientImpossible raw
  in absurd impossible
  where
    absurd : Agda.Builtin.Empty.⊥ → Agda.Builtin.Unit.⊤
    absurd ()
