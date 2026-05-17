module DASHI.Foundations.QuotientSetoidSurface where

open import Agda.Primitive using (Level; Setω; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Non-cubical quotient-by-setoid authority surface.
--
-- This is intentionally an interface, not a HIT quotient construction.  It
-- gives downstream modules a small, explicit place to require quotient
-- soundness and eliminators for an externally supplied setoid quotient.

subst :
  {ℓa ℓp : Level} →
  {A : Set ℓa} →
  (P : A → Set ℓp) →
  {x y : A} →
  x ≡ y →
  P x →
  P y
subst P refl px = px

record IsEquivalence
  {ℓa ℓr : Level}
  {A : Set ℓa}
  (_≈_ : A → A → Set ℓr) :
  Set (ℓa ⊔ ℓr) where
  field
    refl≈ :
      (x : A) →
      x ≈ x

    sym≈ :
      {x y : A} →
      x ≈ y →
      y ≈ x

    trans≈ :
      {x y z : A} →
      x ≈ y →
      y ≈ z →
      x ≈ z

open IsEquivalence public

record SetoidSurface
  (ℓa ℓr : Level) :
  Set (lsuc (ℓa ⊔ ℓr)) where
  field
    Carrier :
      Set ℓa

    _≈_ :
      Carrier →
      Carrier →
      Set ℓr

    isEquivalence :
      IsEquivalence _≈_

open SetoidSurface public

record SetoidQuotientSurface
  {ℓa ℓr : Level}
  (S : SetoidSurface ℓa ℓr)
  (ℓq : Level) :
  Setω where
  field
    QuotientCarrier :
      Set ℓq

    quotientClass :
      Carrier S →
      QuotientCarrier

    quotientSound :
      {x y : Carrier S} →
      _≈_ S x y →
      quotientClass x
      ≡
      quotientClass y

    quotientRec :
      {ℓb : Level} →
      (B : Set ℓb) →
      (f : Carrier S → B) →
      ((x y : Carrier S) →
        _≈_ S x y →
        f x ≡ f y) →
      QuotientCarrier →
      B

    quotientRec-β :
      {ℓb : Level} →
      (B : Set ℓb) →
      (f : Carrier S → B) →
      (resp :
        (x y : Carrier S) →
        _≈_ S x y →
        f x ≡ f y) →
      (x : Carrier S) →
      quotientRec B f resp (quotientClass x)
      ≡
      f x

    quotientElim :
      {ℓp : Level} →
      (P : QuotientCarrier → Set ℓp) →
      (f : (x : Carrier S) → P (quotientClass x)) →
      ((x y : Carrier S) →
        (eq : _≈_ S x y) →
        subst P (quotientSound eq) (f x)
        ≡
        f y) →
      (q : QuotientCarrier) →
      P q

    quotientElim-β :
      {ℓp : Level} →
      (P : QuotientCarrier → Set ℓp) →
      (f : (x : Carrier S) → P (quotientClass x)) →
      (resp :
        (x y : Carrier S) →
        (eq : _≈_ S x y) →
        subst P (quotientSound eq) (f x)
        ≡
        f y) →
      (x : Carrier S) →
      quotientElim P f resp (quotientClass x)
      ≡
      f x

open SetoidQuotientSurface public

quotientStable :
  {ℓa ℓr ℓq : Level} →
  {S : SetoidSurface ℓa ℓr} →
  (Q : SetoidQuotientSurface S ℓq) →
  {x y : Carrier S} →
  _≈_ S x y →
  quotientClass Q x
  ≡
  quotientClass Q y
quotientStable Q eq = quotientSound Q eq

quotientTransport :
  {ℓa ℓr ℓq ℓp : Level} →
  {S : SetoidSurface ℓa ℓr} →
  (Q : SetoidQuotientSurface S ℓq) →
  (P : QuotientCarrier Q → Set ℓp) →
  {x y : Carrier S} →
  _≈_ S x y →
  P (quotientClass Q x) →
  P (quotientClass Q y)
quotientTransport Q P eq px =
  subst P (quotientSound Q eq) px

record SetoidUnaryOperationSurface
  {ℓa ℓr : Level}
  (S : SetoidSurface ℓa ℓr) :
  Set (ℓa ⊔ ℓr) where
  field
    unaryOperation :
      Carrier S →
      Carrier S

    unaryOperationRespects≈ :
      {x y : Carrier S} →
      _≈_ S x y →
      _≈_ S (unaryOperation x) (unaryOperation y)

open SetoidUnaryOperationSurface public

record SetoidBinaryOperationSurface
  {ℓa ℓr : Level}
  (S : SetoidSurface ℓa ℓr) :
  Set (ℓa ⊔ ℓr) where
  field
    binaryOperation :
      Carrier S →
      Carrier S →
      Carrier S

    binaryOperationRespects≈ :
      {x x′ y y′ : Carrier S} →
      _≈_ S x x′ →
      _≈_ S y y′ →
      _≈_ S
        (binaryOperation x y)
        (binaryOperation x′ y′)

open SetoidBinaryOperationSurface public

record SetoidNormSurface
  {ℓa ℓr ℓn : Level}
  (S : SetoidSurface ℓa ℓr)
  (NormValue : Set ℓn) :
  Set (ℓa ⊔ ℓr ⊔ ℓn) where
  field
    norm :
      Carrier S →
      NormValue

    normRespects≈ :
      {x y : Carrier S} →
      _≈_ S x y →
      norm x ≡ norm y

open SetoidNormSurface public

quotientNorm :
  {ℓa ℓr ℓq ℓn : Level} →
  {S : SetoidSurface ℓa ℓr} →
  {NormValue : Set ℓn} →
  (Q : SetoidQuotientSurface S ℓq) →
  SetoidNormSurface S NormValue →
  QuotientCarrier Q →
  NormValue
quotientNorm Q N =
  quotientRec Q
    _
    (SetoidNormSurface.norm N)
    (λ x y eq →
      SetoidNormSurface.normRespects≈ N {x} {y} eq)

quotientNorm-β :
  {ℓa ℓr ℓq ℓn : Level} →
  {S : SetoidSurface ℓa ℓr} →
  {NormValue : Set ℓn} →
  (Q : SetoidQuotientSurface S ℓq) →
  (N : SetoidNormSurface S NormValue) →
  (x : Carrier S) →
  quotientNorm Q N (quotientClass Q x)
  ≡
  SetoidNormSurface.norm N x
quotientNorm-β Q N x =
  quotientRec-β Q
    _
    (SetoidNormSurface.norm N)
    (λ a b eq →
      SetoidNormSurface.normRespects≈ N {a} {b} eq)
    x
