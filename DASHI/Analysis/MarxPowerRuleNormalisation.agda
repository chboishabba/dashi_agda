module DASHI.Analysis.MarxPowerRuleNormalisation where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Primitive using (Set₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.MarxDifferentialCore
open import DASHI.Analysis.MarxPolynomialDifferential
open import DASHI.Analysis.MarxConstructiveRealRingNormalisation

------------------------------------------------------------------------
-- Algebraic laws required to normalize repeated addition into a natural
-- scalar.  The core MarxAlgebra intentionally contains only the identities
-- needed for finite factorisation; this companion owns the stronger semiring
-- normalization used by the displayed n*x^(n-1) formula.

record MarxPowerAlgebraLaws
  (A : MarxAlgebra)
  : Set₁ where
  field
    addZeroLeftLaw : ∀ x → _+_ A (zero A) x ≡ x
    addZeroRightLaw : ∀ x → _+_ A x (zero A) ≡ x
    addAssocLaw : ∀ x y z → _+_ A (_+_ A x y) z ≡ _+_ A x (_+_ A y z)
    mulCommLaw : ∀ x y → _*_ A x y ≡ _*_ A y x
    distribRightLaw :
      ∀ x y z → _*_ A (_+_ A x y) z ≡ _+_ A (_*_ A x z) (_*_ A y z)

open MarxPowerAlgebraLaws public

natCast :
  {A : MarxAlgebra} →
  Nat → Carrier A
natCast {A} zero = zero A
natCast {A} (suc n) = _+_ A (natCast n) (one A)

natScale :
  {A : MarxAlgebra} →
  Nat → Carrier A → Carrier A
natScale {A} n x = _*_ A (natCast n) x

mulZeroLeft :
  {A : MarxAlgebra} →
  MarxPowerAlgebraLaws A →
  ∀ x → _*_ A (zero A) x ≡ zero A
mulZeroLeft {A} L x =
  trans (mulCommLaw L (zero A) x) (mulZeroRight A x)

mulOneLeft :
  {A : MarxAlgebra} →
  MarxPowerAlgebraLaws A →
  ∀ x → _*_ A (one A) x ≡ x
mulOneLeft {A} L x =
  trans (mulCommLaw L (one A) x) (mulOneRight A x)

natCastZero :
  {A : MarxAlgebra} →
  natCast {A} zero ≡ zero A
natCastZero = refl

natCastSuccessor :
  {A : MarxAlgebra} →
  ∀ n → natCast {A} (suc n) ≡ _+_ A (natCast n) (one A)
natCastSuccessor n = refl

natScaleZero :
  {A : MarxAlgebra} →
  (L : MarxPowerAlgebraLaws A) →
  ∀ x → natScale zero x ≡ zero A
natScaleZero L x = mulZeroLeft L x

natScaleOne :
  {A : MarxAlgebra} →
  (L : MarxPowerAlgebraLaws A) →
  ∀ x → natScale (suc zero) x ≡ x
natScaleOne {A} L x =
  trans
    (cong (λ coefficient → _*_ A coefficient x)
      (addZeroLeftLaw L (one A)))
    (mulOneLeft L x)

natScaleSuccessor :
  {A : MarxAlgebra} →
  (L : MarxPowerAlgebraLaws A) →
  ∀ n x →
  natScale (suc n) x ≡ _+_ A (natScale n x) x
natScaleSuccessor {A} L n x =
  trans
    (distribRightLaw L (natCast n) (one A) x)
    (cong₂ (_+_ A) refl (mulOneLeft L x))

natScaleMulRight :
  {A : MarxAlgebra} →
  ∀ n x y →
  _*_ A (natScale n x) y ≡ natScale n (_*_ A x y)
natScaleMulRight {A} n x y = mulAssoc A (natCast n) x y

------------------------------------------------------------------------
-- Exact inductive normalization of the already-constructed recursive power
-- derivative.

normalisePowerDerivativeFromLaws :
  {A : MarxAlgebra} →
  (L : MarxPowerAlgebraLaws A) →
  ∀ n x →
  marxDerivative (powerFactorisation (suc n)) x
  ≡ natScale (suc n) (powerFunction n x)
normalisePowerDerivativeFromLaws {A} L zero x =
  trans
    (powerDerivativeSuccessor zero x)
    (trans
      (cong₂ (_+_ A) (mulZeroLeft L x) refl)
      (trans
        (addZeroLeftLaw L (one A))
        (sym (natScaleOne L (one A)))))
normalisePowerDerivativeFromLaws {A} L (suc n) x =
  trans
    (powerDerivativeSuccessor (suc n) x)
    (trans
      (cong₂
        (_+_ A)
        (cong
          (λ derivative → _*_ A derivative x)
          (normalisePowerDerivativeFromLaws L n x))
        refl)
      (trans
        (cong₂
          (_+_ A)
          (natScaleMulRight
            (suc n)
            (powerFunction n x)
            x)
          refl)
        (sym
          (natScaleSuccessor L
            (suc n)
            (powerFunction (suc n) x)))))

powerRuleNormalisationFromLaws :
  {A : MarxAlgebra} →
  MarxPowerAlgebraLaws A →
  PowerRuleNormalisation A
powerRuleNormalisationFromLaws L =
  record
    { natScale = natScale
    ; zeroScale = natScaleZero L
    ; successorScale = natScaleSuccessor L
    ; normalisePowerDerivative = normalisePowerDerivativeFromLaws L
    }

powerDerivativeNatScale :
  {A : MarxAlgebra} →
  (L : MarxPowerAlgebraLaws A) →
  ∀ n x →
  marxDerivative (powerFactorisation (suc n)) x
  ≡ natScale (suc n) (powerFunction n x)
powerDerivativeNatScale = normalisePowerDerivativeFromLaws

------------------------------------------------------------------------
-- The ordinary constructed-real adapter inherits the power laws directly
-- from its selected real carrier.

constructedRealPowerAlgebraLaws :
  ∀ {R : ConstructedOrderedCompleteReal} →
  (L : ConstructedRealRingNormalisationLaws R) →
  MarxPowerAlgebraLaws (ordinaryConstructiveRealMarxAlgebra L)
constructedRealPowerAlgebraLaws {R} L =
  record
    { addZeroLeftLaw = addZeroLeft R
    ; addZeroRightLaw = addZeroRight R
    ; addAssocLaw = addAssoc R
    ; mulCommLaw = mulComm R
    ; distribRightLaw = distribRight R
    }

ordinaryRealPowerRuleNormalisation :
  ∀ {R : ConstructedOrderedCompleteReal} →
  (L : ConstructedRealRingNormalisationLaws R) →
  PowerRuleNormalisation (ordinaryConstructiveRealMarxAlgebra L)
ordinaryRealPowerRuleNormalisation L =
  powerRuleNormalisationFromLaws (constructedRealPowerAlgebraLaws L)

------------------------------------------------------------------------
-- Structural polynomial differentiation.  This gives an executable normal
-- form even before coefficients are collected into a finite monomial list.

formalPolynomialDerivative :
  {A : MarxAlgebra} →
  Polynomial A → Polynomial A
formalPolynomialDerivative {A} (constant c) = constant (zero A)
formalPolynomialDerivative varTerm = constant (one _)
formalPolynomialDerivative (p +P q) =
  formalPolynomialDerivative p +P formalPolynomialDerivative q
formalPolynomialDerivative (p *P q) =
  (formalPolynomialDerivative p *P q)
  +P (p *P formalPolynomialDerivative q)

polynomialDerivativeInterpretationCommutes :
  {A : MarxAlgebra} →
  (p : Polynomial A) →
  (x : Carrier A) →
  polynomialDerivative p x
  ≡ interpret (formalPolynomialDerivative p) x
polynomialDerivativeInterpretationCommutes (constant c) x = refl
polynomialDerivativeInterpretationCommutes varTerm x = refl
polynomialDerivativeInterpretationCommutes {A} (p +P q) x =
  trans
    (polynomialSumRule p q x)
    (cong₂
      (_+_ A)
      (polynomialDerivativeInterpretationCommutes p x)
      (polynomialDerivativeInterpretationCommutes q x))
polynomialDerivativeInterpretationCommutes {A} (p *P q) x =
  trans
    (polynomialProductRule p q x)
    (cong₂
      (_+_ A)
      (cong
        (λ leftDerivative → _*_ A leftDerivative (interpret q x))
        (polynomialDerivativeInterpretationCommutes p x))
      (cong
        (λ rightDerivative → _*_ A (interpret p x) rightDerivative)
        (polynomialDerivativeInterpretationCommutes q x)))

monomial :
  {A : MarxAlgebra} →
  Carrier A → Nat → Polynomial A
monomial coefficient degree =
  constant coefficient *P powerPolynomial degree

monomialDerivative :
  {A : MarxAlgebra} →
  (coefficient : Carrier A) →
  (degree : Nat) →
  (x : Carrier A) →
  polynomialDerivative (monomial coefficient degree) x
  ≡ interpret (formalPolynomialDerivative (monomial coefficient degree)) x
monomialDerivative coefficient degree x =
  polynomialDerivativeInterpretationCommutes
    (monomial coefficient degree)
    x
