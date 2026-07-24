module DASHI.Analysis.FastCauchyQuotient where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import DASHI.Analysis.FastCauchyReals

------------------------------------------------------------------------
-- Backend-neutral set quotient.  Cubical set quotients, a trusted quotient
-- library, or a project-local quotient implementation may inhabit this record.
-- Downstream arithmetic is then constructed, rather than postulated separately.

record SetQuotientBackend
  (Carrier : Set)
  (_∼_ : Carrier → Carrier → Set) : Set₁ where
  field
    Quotient : Set
    inject : Carrier → Quotient
    sound : ∀ {x y} → x ∼ y → inject x ≡ inject y
    representative : Quotient → Carrier
    representativeCorrect : ∀ q → inject (representative q) ≡ q

    lift₁ :
      ∀ {B : Set}
        (f : Carrier → B) →
      (∀ {x y} → x ∼ y → f x ≡ f y) →
      Quotient → B

    lift₁β :
      ∀ {B : Set}
        (f : Carrier → B)
        (respect : ∀ {x y} → x ∼ y → f x ≡ f y)
        x →
      lift₁ f respect (inject x) ≡ f x

    lift₂ :
      ∀ {B : Set}
        (f : Carrier → Carrier → B) →
      (∀ {x x′ y y′} → x ∼ x′ → y ∼ y′ → f x y ≡ f x′ y′) →
      Quotient → Quotient → B

    lift₂β :
      ∀ {B : Set}
        (f : Carrier → Carrier → B)
        (respect : ∀ {x x′ y y′} → x ∼ x′ → y ∼ y′ → f x y ≡ f x′ y′)
        x y →
      lift₂ f respect (inject x) (inject y) ≡ f x y

open SetQuotientBackend public

------------------------------------------------------------------------
-- Quotient arithmetic generated from representative operations.

record FastCauchyQuotientOperations
  (A : RationalMetricAuthority)
  (O : FastCauchyOperations A)
  (Q : SetQuotientBackend (FastCauchyReal A) _≈R_) : Set₁ where

  zero : Quotient Q
  zero = inject Q (zeroR O)

  one : Quotient Q
  one = inject Q (oneR O)

  neg : Quotient Q → Quotient Q
  neg = lift₁ Q (λ x → inject Q (negR O x))
    (λ x≈y → sound Q (FastCauchyOperations.subRespect O x≈y
      (reflexive (equalityLaws O) (zeroR O))))

  add : Quotient Q → Quotient Q → Quotient Q
  add = lift₂ Q (λ x y → inject Q (addR O x y))
    (λ x≈x′ y≈y′ → sound Q (addRespect O x≈x′ y≈y′))

  sub : Quotient Q → Quotient Q → Quotient Q
  sub = lift₂ Q (λ x y → inject Q (subR O x y))
    (λ x≈x′ y≈y′ → sound Q (subRespect O x≈x′ y≈y′))

  mul : Quotient Q → Quotient Q → Quotient Q
  mul = lift₂ Q (λ x y → inject Q (mulR O x y))
    (λ x≈x′ y≈y′ → sound Q (mulRespect O x≈x′ y≈y′))

  abs : Quotient Q → Quotient Q
  abs = lift₁ Q (λ x → inject Q (absR O x)) absRespect
    where
      absRespect : ∀ {x y} → x ≈R y →
        inject Q (absR O x) ≡ inject Q (absR O y)
      absRespect x≈y = sound Q (absRespectRepresentative x≈y)

      -- Absolute-value respect is kept as a named leaf because the current
      -- `FastCauchyOperations` predates that field.
      absRespectRepresentative : ∀ {x y} → x ≈R y → absR O x ≈R absR O y
      absRespectRepresentative = FastCauchyQuotientOperations.absRespectLeaf

  field
    absRespectLeaf : ∀ {x y} → x ≈R y → absR O x ≈R absR O y

    le lt : Quotient Q → Quotient Q → Set
    leAgrees : ∀ x y → le (inject Q x) (inject Q y) ≡ leR O x y
    ltAgrees : ∀ x y → lt (inject Q x) (inject Q y) ≡ ltR O x y

open FastCauchyQuotientOperations public

------------------------------------------------------------------------
-- Algebraic laws are proved on representatives and transported through the
-- quotient.  This record stores the transported results needed by the existing
-- `ConstructedOrderedCompleteReal` target.

record FastCauchyQuotientAlgebraLaws
  (A : RationalMetricAuthority)
  (O : FastCauchyOperations A)
  (Q : SetQuotientBackend (FastCauchyReal A) _≈R_)
  (F : FastCauchyQuotientOperations A O Q) : Set₁ where
  field
    addAssoc : ∀ a b c → add F (add F a b) c ≡ add F a (add F b c)
    addComm : ∀ a b → add F a b ≡ add F b a
    addZeroLeft : ∀ a → add F (zero F) a ≡ a
    addZeroRight : ∀ a → add F a (zero F) ≡ a

    mulAssoc : ∀ a b c → mul F (mul F a b) c ≡ mul F a (mul F b c)
    mulComm : ∀ a b → mul F a b ≡ mul F b a
    mulOneLeft : ∀ a → mul F (one F) a ≡ a
    mulOneRight : ∀ a → mul F a (one F) ≡ a

    distribLeft : ∀ a b c →
      mul F a (add F b c) ≡ add F (mul F a b) (mul F a c)
    distribRight : ∀ a b c →
      mul F (add F a b) c ≡ add F (mul F a c) (mul F b c)

    subSelf : ∀ a → sub F a a ≡ zero F

open FastCauchyQuotientAlgebraLaws public

record FastCauchyQuotientCompleteness
  (A : RationalMetricAuthority)
  (O : FastCauchyOperations A)
  (Q : SetQuotientBackend (FastCauchyReal A) _≈R_) : Set₁ where
  field
    Sequence : Set
    sequenceAt : Sequence → Nat → Quotient Q
    IsCauchy : Sequence → Set
    ConvergesTo : Sequence → Quotient Q → Set
    cauchyLimit :
      (s : Sequence) →
      IsCauchy s →
      Σ (Quotient Q) (λ x → ConvergesTo s x)

open FastCauchyQuotientCompleteness public

fastCauchyQuotientRealization :
  ∀ {A : RationalMetricAuthority}
    {O : FastCauchyOperations A}
    {Q : SetQuotientBackend (FastCauchyReal A) _≈R_}
    (F : FastCauchyQuotientOperations A O Q) →
  FastCauchyQuotientAlgebraLaws A O Q F →
  FastCauchyQuotientCompleteness A O Q →
  FastCauchyQuotientRealization A O
fastCauchyQuotientRealization {A} {O} {Q} F L C =
  record
    { Real = Quotient Q
    ; quotient = inject Q
    ; quotientSound = sound Q
    ; quotientComplete = λ r → representative Q r , representativeCorrect Q r
    ; zero = zero F
    ; one = one F
    ; add = add F
    ; sub = sub F
    ; mul = mul F
    ; neg = neg F
    ; abs = abs F
    ; le = le F
    ; lt = lt F
    ; operationsAgree = FastCauchyQuotientOperations A O Q
    ; orderedFieldLaws = FastCauchyQuotientAlgebraLaws A O Q F
    ; Sequence = Sequence C
    ; sequenceAt = sequenceAt C
    ; IsCauchy = IsCauchy C
    ; ConvergesTo = ConvergesTo C
    ; cauchyLimit = cauchyLimit C
    ; addAssoc = addAssoc L
    ; addComm = addComm L
    ; addZeroLeft = addZeroLeft L
    ; addZeroRight = addZeroRight L
    ; mulAssoc = mulAssoc L
    ; mulComm = mulComm L
    ; mulOneLeft = mulOneLeft L
    ; mulOneRight = mulOneRight L
    ; distribLeft = distribLeft L
    ; distribRight = distribRight L
    ; subSelf = subSelf L
    }
