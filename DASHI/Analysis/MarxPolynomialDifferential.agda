module DASHI.Analysis.MarxPolynomialDifferential where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; suc) renaming (zero to zeroN)
open import Agda.Primitive using (Set)

open import DASHI.Analysis.MarxDifferentialCore public

------------------------------------------------------------------------
-- Powers are built entirely from the identity and product constructors.

powerFunction :
  {A : MarxAlgebra} →
  Nat → Function A
powerFunction {A} zeroN x = one A
powerFunction {A} (suc n) x =
  _*_ A (powerFunction {A = A} n x) x

powerFactorisation :
  {A : MarxAlgebra} →
  (n : Nat) →
  MarxFactorisation A (powerFunction {A = A} n)
powerFactorisation {A} zeroN = constantFactorisation {A = A} (one A)
powerFactorisation {A} (suc n) =
  productFactorisations {A = A}
    (powerFactorisation {A = A} n)
    (identityFactorisation {A = A})

powerDerivativeZero :
  {A : MarxAlgebra} →
  (x : Carrier A) →
  marxDerivative {A = A} (powerFactorisation {A = A} zeroN) x ≡ zero A
powerDerivativeZero x = refl

powerDerivativeSuccessor :
  {A : MarxAlgebra} →
  (n : Nat) →
  (x : Carrier A) →
  marxDerivative {A = A} (powerFactorisation {A = A} (suc n)) x
  ≡ _+_ A
      (_*_ A
        (marxDerivative {A = A} (powerFactorisation {A = A} n) x)
        x)
      (_*_ A (powerFunction {A = A} n x) (one A))
powerDerivativeSuccessor n x = refl

------------------------------------------------------------------------
-- The displayed n*x^(n-1) normal form requires a natural-scalar policy and
-- algebraic normalisation.  The recursive derivative above is already exact;
-- this record states precisely what is additionally required to print it in
-- the conventional closed form.

record PowerRuleNormalisation
  (A : MarxAlgebra)
  : Set₁ where
  field
    natScale : Nat → Carrier A → Carrier A

    zeroScale :
      ∀ x → natScale zeroN x ≡ zero A

    successorScale :
      ∀ n x →
      natScale (suc n) x
      ≡ _+_ A (natScale n x) x

    normalisePowerDerivative :
      ∀ n x →
      marxDerivative (powerFactorisation {A = A} (suc n)) x
      ≡ natScale (suc n) (powerFunction {A = A} n x)

open PowerRuleNormalisation public

powerRule :
  {A : MarxAlgebra} →
  (N : PowerRuleNormalisation A) →
  (n : Nat) →
  (x : Carrier A) →
  marxDerivative {A = A} (powerFactorisation {A = A} (suc n)) x
  ≡ natScale N (suc n) (powerFunction {A = A} n x)
powerRule {A} N n x = normalisePowerDerivative N n x

------------------------------------------------------------------------
-- A polynomial syntax whose differentiation receipts are constructed by
-- structural recursion rather than asserted after evaluation.

infixl 20 _+P_
infixl 30 _*P_

data Polynomial
  (A : MarxAlgebra)
  : Set where
  constant : Carrier A → Polynomial A
  varTerm : Polynomial A
  _+P_ : Polynomial A → Polynomial A → Polynomial A
  _*P_ : Polynomial A → Polynomial A → Polynomial A

open Polynomial public

interpret :
  {A : MarxAlgebra} →
  Polynomial A → Function A
interpret {A} (constant c) = constantFunction {A = A} c
interpret {A} varTerm = identityFunction {A = A}
interpret {A} (p +P q) = addFunctions {A = A} (interpret {A = A} p) (interpret {A = A} q)
interpret {A} (p *P q) = multiplyFunctions {A = A} (interpret {A = A} p) (interpret {A = A} q)

polynomialFactorisation :
  {A : MarxAlgebra} →
  (p : Polynomial A) →
  MarxFactorisation A (interpret {A = A} p)
polynomialFactorisation {A} (constant c) = constantFactorisation {A = A} c
polynomialFactorisation {A} varTerm = identityFactorisation {A = A}
polynomialFactorisation {A} (p +P q) =
  addFactorisations {A = A}
    (polynomialFactorisation {A = A} p)
    (polynomialFactorisation {A = A} q)
polynomialFactorisation {A} (p *P q) =
  productFactorisations {A = A}
    (polynomialFactorisation {A = A} p)
    (polynomialFactorisation {A = A} q)

polynomialDerivative :
  {A : MarxAlgebra} →
  Polynomial A → Function A
polynomialDerivative {A} p =
  marxDerivative {A = A} (polynomialFactorisation {A = A} p)

polynomialConstantRule :
  {A : MarxAlgebra} →
  (c x : Carrier A) →
  polynomialDerivative {A = A} (constant c) x ≡ zero A
polynomialConstantRule c x = refl

polynomialVariableRule :
  {A : MarxAlgebra} →
  (x : Carrier A) →
  polynomialDerivative {A = A} varTerm x ≡ one A
polynomialVariableRule x = refl

polynomialSumRule :
  {A : MarxAlgebra} →
  (p q : Polynomial A) →
  (x : Carrier A) →
  polynomialDerivative {A = A} (p +P q) x
  ≡ _+_ A
      (polynomialDerivative {A = A} p x)
      (polynomialDerivative {A = A} q x)
polynomialSumRule p q x = refl

polynomialProductRule :
  {A : MarxAlgebra} →
  (p q : Polynomial A) →
  (x : Carrier A) →
  polynomialDerivative {A = A} (p *P q) x
  ≡ _+_ A
      (_*_ A (polynomialDerivative {A = A} p x) (interpret {A = A} q x))
      (_*_ A (interpret {A = A} p x) (polynomialDerivative {A = A} q x))
polynomialProductRule p q x = refl

powerPolynomial :
  {A : MarxAlgebra} →
  Nat → Polynomial A
powerPolynomial {A} zeroN = constant (one A)
powerPolynomial {A} (suc n) = powerPolynomial {A} n *P varTerm

powerPolynomialInterpretsAsPower :
  {A : MarxAlgebra} →
  (n : Nat) →
  (x : Carrier A) →
  interpret {A = A} (powerPolynomial {A = A} n) x ≡ powerFunction {A = A} n x
powerPolynomialInterpretsAsPower {A} zeroN x = refl
powerPolynomialInterpretsAsPower {A} (suc n) x =
  cong (λ y → _*_ A y x)
    (powerPolynomialInterpretsAsPower {A = A} n x)
