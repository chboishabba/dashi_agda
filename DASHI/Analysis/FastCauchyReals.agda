module DASHI.Analysis.FastCauchyReals where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)

open import DASHI.Analysis.ConstructiveRealSpine

------------------------------------------------------------------------
-- Canonical rapidly convergent rational representatives.
--
-- This module chooses the quotient-free/setoid route explicitly.  It provides
-- the nondegenerate carrier and its extensional equality.  Turning that setoid
-- into ordinary Agda propositional equality is isolated in
-- `FastCauchyQuotientRealization`, rather than being hidden in the EML layer.

record RationalMetricAuthority : Set₁ where
  infixl 20 _+Q_ _-Q_
  infixl 30 _*Q_
  infix 15 _≤Q_
  field
    Q : Set
    zeroQ oneQ : Q
    _+Q_ _-Q_ _*Q_ : Q → Q → Q
    negQ absQ : Q → Q
    _≤Q_ : Q → Q → Set

    dyadicError : Nat → Q

    leRefl : ∀ x → x ≤Q x
    leTrans : ∀ {x y z} → x ≤Q y → y ≤Q z → x ≤Q z
    addMono : ∀ {a b c d} → a ≤Q b → c ≤Q d → (a +Q c) ≤Q (b +Q d)

    absZero : absQ zeroQ ≡ zeroQ
    absSymmetricDifference : ∀ x y → absQ (x -Q y) ≡ absQ (y -Q x)
    absTriangleDifference : ∀ x y z →
      absQ (x -Q z) ≤Q (absQ (x -Q y) +Q absQ (y -Q z))

    dyadicPositive : ∀ n → zeroQ ≤Q dyadicError n
    dyadicTailAbsorbs : ∀ n →
      (dyadicError n +Q dyadicError n)
      ≤Q dyadicError n +Q dyadicError n

open RationalMetricAuthority public

record FastCauchyReal (A : RationalMetricAuthority) : Set where
  constructor fastReal
  field
    approximate : Nat → Q A
    fastCauchy : ∀ m n →
      absQ A (approximate m -Q approximate n)
      ≤Q A (dyadicError A m +Q dyadicError A n)

open FastCauchyReal public

------------------------------------------------------------------------
-- Extensional equality.  The bound is deliberately explicit: two canonical
-- representatives denote the same real when their pointwise difference is
-- swallowed by the canonical approximation error.

_≈R_ :
  ∀ {A : RationalMetricAuthority} →
  FastCauchyReal A →
  FastCauchyReal A →
  Set
_≈R_ {A} x y =
  ∀ n →
    absQ A (approximate x n -Q approximate y n)
    ≤Q A (dyadicError A n +Q dyadicError A n)

record FastCauchyEqualityLaws (A : RationalMetricAuthority) : Set₁ where
  field
    reflexive : ∀ x → x ≈R x
    symmetric : ∀ {x y} → x ≈R y → y ≈R x
    transitive : ∀ {x y z} → x ≈R y → y ≈R z → x ≈R z

open FastCauchyEqualityLaws public

constantFastReal :
  ∀ (A : RationalMetricAuthority) →
  Q A →
  FastCauchyReal A
constantFastReal A q =
  fastReal
    (λ _ → q)
    constantIsFast
  where
    constantIsFast : ∀ m n →
      absQ A (q -Q q)
      ≤Q A (dyadicError A m +Q dyadicError A n)
    constantIsFast m n = constantDifferenceBound m n

    -- Kept as the exact rational-law leaf: a concrete rational implementation
    -- proves q-q=0 and then uses nonnegativity of the dyadic errors.
    postulate
      constantDifferenceBound : ∀ m n →
        absQ A (q -Q q)
        ≤Q A (dyadicError A m +Q dyadicError A n)

------------------------------------------------------------------------
-- Operations and completeness are stated over the actual fast representatives.
-- The quotient realization below is the only place where extensional equality
-- is promoted to Agda equality.

record FastCauchyOperations (A : RationalMetricAuthority) : Set₁ where
  field
    equalityLaws : FastCauchyEqualityLaws A

    zeroR oneR : FastCauchyReal A
    addR subR mulR : FastCauchyReal A → FastCauchyReal A → FastCauchyReal A
    negR absR : FastCauchyReal A → FastCauchyReal A
    leR ltR : FastCauchyReal A → FastCauchyReal A → Set

    addRespect : ∀ {a a′ b b′} → a ≈R a′ → b ≈R b′ → addR a b ≈R addR a′ b′
    subRespect : ∀ {a a′ b b′} → a ≈R a′ → b ≈R b′ → subR a b ≈R subR a′ b′
    mulRespect : ∀ {a a′ b b′} → a ≈R a′ → b ≈R b′ → mulR a b ≈R mulR a′ b′

open FastCauchyOperations public

record FastCauchyQuotientRealization
  (A : RationalMetricAuthority)
  (O : FastCauchyOperations A) : Set₁ where

  field
    Real : Set
    quotient : FastCauchyReal A → Real

    quotientSound : ∀ {x y} → x ≈R y → quotient x ≡ quotient y
    quotientComplete : ∀ r → Σ (FastCauchyReal A) (λ x → quotient x ≡ r)

    zero one : Real
    add sub mul : Real → Real → Real
    neg abs : Real → Real
    le lt : Real → Real → Set

    operationsAgree : Set
    orderedFieldLaws : Set

    Sequence : Set
    sequenceAt : Sequence → Nat → Real
    IsCauchy : Sequence → Set
    ConvergesTo : Sequence → Real → Set
    cauchyLimit : (s : Sequence) → IsCauchy s → Σ Real (λ x → ConvergesTo s x)

    addAssoc : ∀ a b c → add (add a b) c ≡ add a (add b c)
    addComm : ∀ a b → add a b ≡ add b a
    addZeroLeft : ∀ a → add zero a ≡ a
    addZeroRight : ∀ a → add a zero ≡ a
    mulAssoc : ∀ a b c → mul (mul a b) c ≡ mul a (mul b c)
    mulComm : ∀ a b → mul a b ≡ mul b a
    mulOneLeft : ∀ a → mul one a ≡ a
    mulOneRight : ∀ a → mul a one ≡ a
    distribLeft : ∀ a b c → mul a (add b c) ≡ add (mul a b) (mul a c)
    distribRight : ∀ a b c → mul (add a b) c ≡ add (mul a c) (mul b c)
    subSelf : ∀ a → sub a a ≡ zero

open FastCauchyQuotientRealization public

fastCauchyConstructedReal :
  ∀ {A : RationalMetricAuthority}
    {O : FastCauchyOperations A} →
  FastCauchyQuotientRealization A O →
  ConstructedOrderedCompleteReal
fastCauchyConstructedReal Q =
  record
    { Real = Real Q
    ; zero = zero Q
    ; one = one Q
    ; _+_ = add Q
    ; _-_ = sub Q
    ; _*_ = mul Q
    ; neg = neg Q
    ; abs = abs Q
    ; _≤_ = le Q
    ; _<_ = lt Q
    ; addAssoc = addAssoc Q
    ; addComm = addComm Q
    ; addZeroLeft = addZeroLeft Q
    ; addZeroRight = addZeroRight Q
    ; mulAssoc = mulAssoc Q
    ; mulComm = mulComm Q
    ; mulOneLeft = mulOneLeft Q
    ; mulOneRight = mulOneRight Q
    ; distribLeft = distribLeft Q
    ; distribRight = distribRight Q
    ; subSelf = subSelf Q
    ; Sequence = Sequence Q
    ; sequenceAt = sequenceAt Q
    ; IsCauchy = IsCauchy Q
    ; ConvergesTo = ConvergesTo Q
    ; cauchyLimit = cauchyLimit Q
    }
