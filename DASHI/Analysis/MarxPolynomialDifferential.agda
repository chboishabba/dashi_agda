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
  _*_ A (powerFunction n x) x

powerFactorisation :
  {A : MarxAlgebra} →
  (n : Nat) →
  MarxFactorisation A (powerFunction n)
powerFactorisation {A} zeroN = constantFactorisation (one A)
powerFactorisation {A} (suc n) =
  productFactorisations
    (powerFactorisation n)
    identityFactorisation

powerDerivativeZero :
  {A : MarxAlgebra} →
  (x : Carrier A) →
  marxDerivative (powerFactorisation zeroN) x ≡ zero A
powerDerivativeZero x = refl

powerDerivativeSuccessor :
  {A : MarxAlgebra} →
  (n : Nat) →
  (x : Carrier A) →
  marxDerivative (powerFactorisation (suc n)) x
  ≡ _+_ A
      (_*_ A
        (marxDerivative (powerFactorisation n) x)
        x)
      (powerFunction n x)
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
      marxDerivative (powerFactorisation (suc n)) x
      ≡ natScale (suc n) (powerFunction n x)

open PowerRuleNormalisation public

powerRule :
  {A : MarxAlgebra} →
  (N : PowerRuleNormalisation A) →
  (n : Nat) →
  (x : Carrier A) →
  marxDerivative (powerFactorisation (suc n)) x
  ≡ natScale N (suc n) (powerFunction n x)
powerRule N n x = normalisePowerDerivative N n x

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
interpret (constant c) = constantFunction c
interpret varTerm = identityFunction
interpret (p +P q) = addFunctions (interpret p) (interpret q)
interpret (p *P q) = multiplyFunctions (interpret p) (interpret q)

polynomialFactorisation :
  {A : MarxAlgebra} →
  (p : Polynomial A) →
  MarxFactorisation A (interpret p)
polynomialFactorisation (constant c) = constantFactorisation c
polynomialFactorisation varTerm = identityFactorisation
polynomialFactorisation (p +P q) =
  addFactorisations
    (polynomialFactorisation p)
    (polynomialFactorisation q)
polynomialFactorisation (p *P q) =
  productFactorisations
    (polynomialFactorisation p)
    (polynomialFactorisation q)

polynomialDerivative :
  {A : MarxAlgebra} →
  Polynomial A → Function A
polynomialDerivative p =
  marxDerivative (polynomialFactorisation p)

polynomialConstantRule :
  {A : MarxAlgebra} →
  (c x : Carrier A) →
  polynomialDerivative (constant c) x ≡ zero A
polynomialConstantRule c x = refl

polynomialVariableRule :
  {A : MarxAlgebra} →
  (x : Carrier A) →
  polynomialDerivative varTerm x ≡ one A
polynomialVariableRule x = refl

polynomialSumRule :
  {A : MarxAlgebra} →
  (p q : Polynomial A) →
  (x : Carrier A) →
  polynomialDerivative (p +P q) x
  ≡ _+_ A
      (polynomialDerivative p x)
      (polynomialDerivative q x)
polynomialSumRule p q x = refl

polynomialProductRule :
  {A : MarxAlgebra} →
  (p q : Polynomial A) →
  (x : Carrier A) →
  polynomialDerivative (p *P q) x
  ≡ _+_ A
      (_*_ A (polynomialDerivative p x) (interpret q x))
      (_*_ A (interpret p x) (polynomialDerivative q x))
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
  interpret (powerPolynomial n) x ≡ powerFunction n x
powerPolynomialInterpretsAsPower zeroN x = refl
powerPolynomialInterpretsAsPower {A} (suc n) x =
  cong (λ y → _*_ A y x)
    (powerPolynomialInterpretsAsPower n x)
