module DASHI.Analysis.MarxReciprocalQuotientNormalisation where

open import Agda.Primitive using (Set; Set₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import DASHI.Analysis.MarxDifferentialCore

------------------------------------------------------------------------
-- Field-level reciprocal laws.  Reciprocal is total as an operation, while
-- every identity that uses it carries an explicit Nonzero receipt.

record MarxReciprocalLaws
  (A : MarxAlgebra)
  : Set₁ where
  field
    Nonzero : Carrier A → Set
    neg : Carrier A → Carrier A
    reciprocal : Carrier A → Carrier A

    reciprocalNonzero :
      ∀ {x} → Nonzero x → Nonzero (reciprocal x)

    mulReciprocalLeft :
      ∀ x → Nonzero x → _*_ A (reciprocal x) x ≡ one A

    mulReciprocalRight :
      ∀ x → Nonzero x → _*_ A x (reciprocal x) ≡ one A

    reciprocalDifferenceIdentity :
      ∀ y y₁ →
      Nonzero y →
      Nonzero y₁ →
      _-_ A (reciprocal y₁) (reciprocal y)
      ≡ _*_ A
          (_*_ A (neg (_-_ A y₁ y)) (reciprocal y))
          (reciprocal y₁)

    reciprocalDifferenceFactor :
      ∀ {x x₁ y y₁ G} →
      _-_ A y₁ y ≡ _*_ A (_-_ A x₁ x) G →
      Nonzero y →
      Nonzero y₁ →
      _-_ A (reciprocal y₁) (reciprocal y)
      ≡ _*_ A
          (_-_ A x₁ x)
          (_*_ A
            (_*_ A (neg G) (reciprocal y))
            (reciprocal y₁))

    reciprocalDiagonalNormalisation :
      ∀ d y →
      Nonzero y →
      _*_ A (_*_ A (neg d) (reciprocal y)) (reciprocal y)
      ≡ _*_ A (neg d) (reciprocal (_*_ A y y))

open MarxReciprocalLaws public

canonicalReciprocalStructure :
  {A : MarxAlgebra} →
  MarxReciprocalLaws A →
  ReciprocalStructure A
canonicalReciprocalStructure L =
  record
    { Nonzero = Nonzero L
    ; reciprocal = λ x _ → reciprocal L x
    }

reciprocalFunction :
  {A : MarxAlgebra} →
  (L : MarxReciprocalLaws A) →
  Function A → Function A
reciprocalFunction L g x = reciprocal L (g x)

reciprocalMarxFactorisation :
  {A : MarxAlgebra} →
  (L : MarxReciprocalLaws A) →
  {g : Function A} →
  (G : MarxFactorisation A g) →
  (nonzero : ∀ x → Nonzero L (g x)) →
  MarxFactorisation A (reciprocalFunction L g)
reciprocalMarxFactorisation {A} L {g} G nonzero =
  record
    { preliminary = λ x x₁ →
        _*_ A
          (_*_ A
            (neg L (preliminary G x x₁))
            (reciprocal L (g x)))
          (reciprocal L (g x₁))
    ; finiteFactorisation = λ x x₁ →
        reciprocalDifferenceFactor L
          (finiteFactorisation G x x₁)
          (nonzero x)
          (nonzero x₁)
    }

canonicalReciprocalFactorisation :
  {A : MarxAlgebra} →
  (L : MarxReciprocalLaws A) →
  {g : Function A} →
  (G : MarxFactorisation A g) →
  (nonzero : ∀ x → Nonzero L (g x)) →
  ReciprocalFactorisation
    (canonicalReciprocalStructure L)
    g
    nonzero
canonicalReciprocalFactorisation L G nonzero =
  record { receipt = reciprocalMarxFactorisation L G nonzero }

reciprocalDerivative :
  {A : MarxAlgebra} →
  (L : MarxReciprocalLaws A) →
  {g : Function A} →
  (G : MarxFactorisation A g) →
  (nonzero : ∀ x → Nonzero L (g x)) →
  (x : Carrier A) →
  marxDerivative (reciprocalMarxFactorisation L G nonzero) x
  ≡ _*_ A
      (_*_ A
        (neg L (marxDerivative G x))
        (reciprocal L (g x)))
      (reciprocal L (g x))
reciprocalDerivative L G nonzero x = refl

reciprocalDerivativeDenominatorSquared :
  {A : MarxAlgebra} →
  (L : MarxReciprocalLaws A) →
  {g : Function A} →
  (G : MarxFactorisation A g) →
  (nonzero : ∀ x → Nonzero L (g x)) →
  (x : Carrier A) →
  marxDerivative (reciprocalMarxFactorisation L G nonzero) x
  ≡ _*_ A
      (neg L (marxDerivative G x))
      (reciprocal L (_*_ A (g x) (g x)))
reciprocalDerivativeDenominatorSquared L G nonzero x =
  trans
    (reciprocalDerivative L G nonzero x)
    (reciprocalDiagonalNormalisation L
      (marxDerivative G x)
      (g x)
      (nonzero x))

------------------------------------------------------------------------
-- Quotient rule, assembled through the existing product-factorisation route.

quotientFactorisationCanonical :
  {A : MarxAlgebra} →
  (L : MarxReciprocalLaws A) →
  {f g : Function A} →
  (F : MarxFactorisation A f) →
  (G : MarxFactorisation A g) →
  (nonzero : ∀ x → Nonzero L (g x)) →
  MarxFactorisation A
    (quotientFunction
      (canonicalReciprocalStructure L)
      f g nonzero)
quotientFactorisationCanonical L F G nonzero =
  quotientFactorisation
    (canonicalReciprocalStructure L)
    nonzero
    F
    (canonicalReciprocalFactorisation L G nonzero)

quotientDerivativeProductForm :
  {A : MarxAlgebra} →
  (L : MarxReciprocalLaws A) →
  {f g : Function A} →
  (F : MarxFactorisation A f) →
  (G : MarxFactorisation A g) →
  (nonzero : ∀ x → Nonzero L (g x)) →
  (x : Carrier A) →
  marxDerivative (quotientFactorisationCanonical L F G nonzero) x
  ≡ _+_ A
      (_*_ A (marxDerivative F x) (reciprocal L (g x)))
      (_*_ A
        (f x)
        (_*_ A
          (_*_ A
            (neg L (marxDerivative G x))
            (reciprocal L (g x)))
          (reciprocal L (g x))))
quotientDerivativeProductForm L F G nonzero x = refl

record QuotientDenominatorSquareNormalisation
  {A : MarxAlgebra}
  (L : MarxReciprocalLaws A)
  : Set₁ where
  field
    quotientNumeratorNormalisation :
      ∀ f g df dg x →
      Nonzero L (g x) →
      _+_ A
        (_*_ A (df x) (reciprocal L (g x)))
        (_*_ A
          (f x)
          (_*_ A
            (_*_ A (neg L (dg x)) (reciprocal L (g x)))
            (reciprocal L (g x))))
      ≡ _*_ A
          (_-_ A
            (_*_ A (g x) (df x))
            (_*_ A (f x) (dg x)))
          (reciprocal L (_*_ A (g x) (g x)))

open QuotientDenominatorSquareNormalisation public

quotientRule :
  {A : MarxAlgebra} →
  (L : MarxReciprocalLaws A) →
  (N : QuotientDenominatorSquareNormalisation L) →
  {f g : Function A} →
  (F : MarxFactorisation A f) →
  (G : MarxFactorisation A g) →
  (nonzero : ∀ x → Nonzero L (g x)) →
  (x : Carrier A) →
  marxDerivative (quotientFactorisationCanonical L F G nonzero) x
  ≡ _*_ A
      (_-_ A
        (_*_ A (g x) (marxDerivative F x))
        (_*_ A (f x) (marxDerivative G x)))
      (reciprocal L (_*_ A (g x) (g x)))
quotientRule L N F G nonzero x =
  trans
    (quotientDerivativeProductForm L F G nonzero x)
    (quotientNumeratorNormalisation N
      f g
      (marxDerivative F)
      (marxDerivative G)
      x
      (nonzero x))

------------------------------------------------------------------------
-- Local nonzero transport.  Analytic quotient theorems can consume this
-- instead of requiring a global nonzero hypothesis on the denominator.

record LocallyNonzeroAt
  {A : MarxAlgebra}
  (L : MarxReciprocalLaws A)
  (g : Function A)
  (x : Carrier A)
  : Set₁ where
  field
    Near : Carrier A → Set
    centreIsNear : Near x
    nonzeroPersistsNear :
      ∀ y → Near y → Nonzero L (g y)

open LocallyNonzeroAt public

nonzeroAtCentre :
  {A : MarxAlgebra} →
  {L : MarxReciprocalLaws A} →
  {g : Function A} →
  {x : Carrier A} →
  LocallyNonzeroAt L g x →
  Nonzero L (g x)
nonzeroAtCentre local =
  nonzeroPersistsNear local _ (centreIsNear local)
