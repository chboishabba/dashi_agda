module DASHI.Analysis.FastCauchyReals where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Agda.Builtin.Nat using (Nat; suc) renaming (zero to zeroN)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)

open import DASHI.Analysis.ConstructiveRealSpine using (ConstructedOrderedCompleteReal)

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

    subSelfQ : ∀ q → q -Q q ≡ zeroQ
    absZero : absQ zeroQ ≡ zeroQ
    absSymmetricDifference : ∀ x y → absQ (x -Q y) ≡ absQ (y -Q x)
    absTriangleDifference : ∀ x y z →
      absQ (x -Q z) ≤Q (absQ (x -Q y) +Q absQ (y -Q z))

    dyadicPositive : ∀ n → zeroQ ≤Q dyadicError n
    zeroBelowDyadicSum : ∀ m n →
      zeroQ ≤Q (dyadicError m +Q dyadicError n)

    dyadicAntitone : ∀ {m n} → m ≤ n → dyadicError n ≤Q dyadicError m
    dyadicDoubleStep : ∀ n →
      (dyadicError (suc n) +Q dyadicError (suc n)) ≡ dyadicError n

open RationalMetricAuthority public

record FastCauchyReal (A : RationalMetricAuthority) : Set where
  constructor fastReal
  field
    approximate : Nat → Q A
    fastCauchy : ∀ m n →
      _≤Q_ A
        (absQ A (_-Q_ A (approximate m) (approximate n)))
        (_+Q_ A (dyadicError A m) (dyadicError A n))

open FastCauchyReal public

------------------------------------------------------------------------
-- Elementary natural-number infrastructure used to choose a common cutoff.

maxN : Nat → Nat → Nat
maxN zeroN n = n
maxN (suc m) zeroN = suc m
maxN (suc m) (suc n) = suc (maxN m n)

reflexiveN : ∀ k → k ≤ k
reflexiveN zeroN = z≤n
reflexiveN (suc k) = s≤s (reflexiveN k)

left≤max : ∀ m n → m ≤ maxN m n
left≤max zeroN n = z≤n
left≤max (suc m) zeroN = reflexiveN (suc m)
left≤max (suc m) (suc n) = s≤s (left≤max m n)

right≤max : ∀ m n → n ≤ maxN m n
right≤max zeroN n = reflexiveN n
right≤max (suc m) zeroN = z≤n
right≤max (suc m) (suc n) = s≤s (right≤max m n)

≤N-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤N-trans z≤n _ = z≤n
≤N-trans (s≤s a≤b) (s≤s b≤c) = s≤s (≤N-trans a≤b b≤c)

------------------------------------------------------------------------
-- Extensional equality.
--
-- A fixed multiplicative error bound is not transitive.  The correct relation
-- quantifies over every requested dyadic precision and permits a common tail
-- cutoff.  Transitivity then requests precision n+1 from both premises and
-- uses 2 ε(n+1) = ε(n).

_≈R_ :
  ∀ {A : RationalMetricAuthority} →
  FastCauchyReal A →
  FastCauchyReal A →
  Set
_≈R_ {A} x y =
  ∀ precision →
  Σ Nat
    (λ cutoff →
      ∀ m n →
      cutoff ≤ m →
      cutoff ≤ n →
      _≤Q_ A
        (absQ A (_-Q_ A (approximate x m) (approximate y n)))
        (dyadicError A precision))

record FastCauchyEqualityLaws (A : RationalMetricAuthority) : Set₁ where
  field
    reflexive : ∀ x → _≈R_ {A} x x
    symmetric : ∀ {x y} → _≈R_ {A} x y → _≈R_ {A} y x
    transitive : ∀ {x y z} → _≈R_ {A} x y → _≈R_ {A} y z → _≈R_ {A} x z

open FastCauchyEqualityLaws public

fastCauchyReflexive :
  ∀ {A : RationalMetricAuthority} →
  (x : FastCauchyReal A) →
  x ≈R x
fastCauchyReflexive {A} x precision =
  suc precision , λ m n cutoff≤m cutoff≤n →
    leTrans A
      (fastCauchy x m n)
      (subst
        (λ upper →
          _≤Q_ A
            (_+Q_ A (dyadicError A m) (dyadicError A n))
            upper)
        (dyadicDoubleStep A precision)
        (addMono A
          (dyadicAntitone A cutoff≤m)
          (dyadicAntitone A cutoff≤n)))

fastCauchySymmetric :
  ∀ {A : RationalMetricAuthority} →
  ∀ {x y : FastCauchyReal A} →
  x ≈R y →
  y ≈R x
fastCauchySymmetric {A} {x} {y} x≈y precision with x≈y precision
... | cutoff , close =
  cutoff , λ m n cutoff≤m cutoff≤n →
    subst
      (λ lower → _≤Q_ A lower (dyadicError A precision))
      (absSymmetricDifference A (approximate x n) (approximate y m))
      (close n m cutoff≤n cutoff≤m)

fastCauchyTransitive :
  ∀ {A : RationalMetricAuthority} →
  ∀ {x y z : FastCauchyReal A} →
  x ≈R y →
  y ≈R z →
  x ≈R z
fastCauchyTransitive {A} {x} {y} {z} x≈y y≈z precision
  with x≈y (suc precision) | y≈z (suc precision)
... | cutoffXY , closeXY | cutoffYZ , closeYZ =
  common , closeXZ
  where
    common : Nat
    common = maxN cutoffXY cutoffYZ

    cutoffXY≤common : cutoffXY ≤ common
    cutoffXY≤common = left≤max cutoffXY cutoffYZ

    cutoffYZ≤common : cutoffYZ ≤ common
    cutoffYZ≤common = right≤max cutoffXY cutoffYZ

    closeXZ : ∀ m n → common ≤ m → common ≤ n →
      _≤Q_ A
        (absQ A (_-Q_ A (approximate x m) (approximate z n)))
        (dyadicError A precision)
    closeXZ m n common≤m common≤n =
      leTrans A
        (absTriangleDifference A
          (approximate x m)
          (approximate y common)
          (approximate z n))
        (subst
          (λ upper →
            _≤Q_ A
              (_+Q_ A
                (absQ A (_-Q_ A (approximate x m) (approximate y common)))
                (absQ A (_-Q_ A (approximate y common) (approximate z n))))
              upper)
          (dyadicDoubleStep A precision)
          (addMono A
            (closeXY
              m common
              (≤N-trans cutoffXY≤common common≤m)
              cutoffXY≤common)
            (closeYZ
              common n
              cutoffYZ≤common
              (≤N-trans cutoffYZ≤common common≤n))))

canonicalFastCauchyEqualityLaws :
  ∀ (A : RationalMetricAuthority) →
  FastCauchyEqualityLaws A
FastCauchyEqualityLaws.reflexive (canonicalFastCauchyEqualityLaws A) x =
  fastCauchyReflexive {A} x
FastCauchyEqualityLaws.symmetric (canonicalFastCauchyEqualityLaws A) {x} {y} rel =
  fastCauchySymmetric {A} {x} {y} rel
FastCauchyEqualityLaws.transitive (canonicalFastCauchyEqualityLaws A) {x} {y} {z} r1 r2 =
  fastCauchyTransitive {A} {x} {y} {z} r1 r2

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
      _≤Q_ A
        (absQ A (_-Q_ A q q))
        (_+Q_ A (dyadicError A m) (dyadicError A n))
    constantIsFast m n
      rewrite subSelfQ A q
            | absZero A =
      zeroBelowDyadicSum A m n

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

open FastCauchyQuotientRealization

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
