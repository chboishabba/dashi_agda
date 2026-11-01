module DASHI.Analysis.MarxConstructiveRealTopology where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ)
open import Agda.Primitive using (Set)
open import Data.Empty using (⊥)
open import Data.Nat.Base using () renaming (_≤_ to _≤N_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; trans; cong)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.MarxDifferentialCore
open import DASHI.Analysis.MarxConstructiveRealRingNormalisation
open import DASHI.Analysis.MarxOrdinaryDerivativeBridge

------------------------------------------------------------------------
-- Absolute value and the induced metric on the selected constructed real.

record ConstructedRealAbsoluteValueLaws
  (R : ConstructedOrderedCompleteReal)
  : Set₁ where
  field
    absNonnegative :
      ∀ x → _≤_ R (zero R) (abs R x)

    absZero :
      abs R (zero R) ≡ zero R

    absZeroOnly :
      ∀ x → abs R x ≡ zero R → x ≡ zero R

    absNeg :
      ∀ x → abs R (neg R x) ≡ abs R x

    absMul :
      ∀ x y →
      abs R (_*_ R x y) ≡ _*_ R (abs R x) (abs R y)

    absTriangle :
      ∀ x y →
      _≤_ R
        (abs R (_+_ R x y))
        (_+_ R (abs R x) (abs R y))

    absSubSymmetric :
      ∀ x y →
      abs R (_-_ R x y) ≡ abs R (_-_ R y x)

    absSubTriangle :
      ∀ x y z →
      _≤_ R
        (abs R (_-_ R x z))
        (_+_ R
          (abs R (_-_ R x y))
          (abs R (_-_ R y z)))

open ConstructedRealAbsoluteValueLaws public

distance :
  (R : ConstructedOrderedCompleteReal) →
  Real R → Real R → Real R
distance R x y = abs R (_-_ R x y)

record ConstructedRealMetricLaws
  (R : ConstructedOrderedCompleteReal)
  (A : ConstructedRealAbsoluteValueLaws R)
  : Set₁ where
  field
    distanceRefl : ∀ x → distance R x x ≡ zero R
    distanceSym : ∀ x y → distance R x y ≡ distance R y x
    distanceTriangle :
      ∀ x y z →
      _≤_ R
        (distance R x z)
        (_+_ R (distance R x y) (distance R y z))

open ConstructedRealMetricLaws public

constructedRealMetricLaws :
  (R : ConstructedOrderedCompleteReal) →
  (A : ConstructedRealAbsoluteValueLaws R) →
  ConstructedRealMetricLaws R A
constructedRealMetricLaws R A =
  record
    { distanceRefl = λ x →
        trans
          (cong (abs R) (subSelf R x))
          (absZero A)
    ; distanceSym = absSubSymmetric A
    ; distanceTriangle = absSubTriangle A
    }

------------------------------------------------------------------------
-- Sequential limit algebra on the already-selected sequence carrier.

record ConstructedRealSequentialLimitLaws
  (R : ConstructedOrderedCompleteReal)
  : Set₁ where
  field
    constantSequence : Real R → Sequence R
    constantSequenceAt :
      ∀ x n → sequenceAt R (constantSequence x) n ≡ x

    mapSequence :
      (Real R → Real R) → Sequence R → Sequence R
    mapSequenceAt :
      ∀ f sequence n →
      sequenceAt R (mapSequence f sequence) n
      ≡ f (sequenceAt R sequence n)

    addSequence : Sequence R → Sequence R → Sequence R
    addSequenceAt :
      ∀ left right n →
      sequenceAt R (addSequence left right) n
      ≡ _+_ R
          (sequenceAt R left n)
          (sequenceAt R right n)

    mulSequence : Sequence R → Sequence R → Sequence R
    mulSequenceAt :
      ∀ left right n →
      sequenceAt R (mulSequence left right) n
      ≡ _*_ R
          (sequenceAt R left n)
          (sequenceAt R right n)

    constantLimit :
      ∀ x → ConvergesTo R (constantSequence x) x

    sumLimit :
      ∀ {left right x y} →
      ConvergesTo R left x →
      ConvergesTo R right y →
      ConvergesTo R (addSequence left right) (_+_ R x y)

    productLimit :
      ∀ {left right x y} →
      ConvergesTo R left x →
      ConvergesTo R right y →
      ConvergesTo R (mulSequence left right) (_*_ R x y)

    limitUnique :
      ∀ {sequence x y} →
      ConvergesTo R sequence x →
      ConvergesTo R sequence y →
      x ≡ y

open ConstructedRealSequentialLimitLaws public

TendsToZeroSequence :
  (R : ConstructedOrderedCompleteReal) →
  Sequence R → Set
TendsToZeroSequence R sequence =
  ConvergesTo R sequence (zero R)

ContinuousAtSequentially :
  (R : ConstructedOrderedCompleteReal) →
  ConstructedRealSequentialLimitLaws R →
  (Real R → Real R) →
  Real R → Set
ContinuousAtSequentially R L f x =
  ∀ sequence →
  ConvergesTo R sequence x →
  ConvergesTo R (mapSequence L f sequence) (f x)

------------------------------------------------------------------------
-- Punctured approaches and little-o normalization.

record PuncturedApproach
  (R : ConstructedOrderedCompleteReal)
  : Set₁ where
  field
    parameters : Sequence R
    tendsToZero : ConvergesTo R parameters (zero R)
    eventuallyNonzero :
      Σ Nat
        (λ cutoff →
          ∀ n →
          cutoff ≤N n →
          sequenceAt R parameters n ≡ zero R → ⊥)

open PuncturedApproach public

record ConstructedRealPuncturedTopology
  (R : ConstructedOrderedCompleteReal)
  : Set₂ where
  field
    limits : ConstructedRealSequentialLimitLaws R
    Nonzero : Real R → Set
    normaliseRemainder : Real R → Real R → Real R

    normalisedAlong :
      (Real R → Real R) →
      PuncturedApproach R →
      Sequence R

    normalisedAlongAt :
      ∀ remainder approach n →
      sequenceAt R (normalisedAlong remainder approach) n
      ≡ normaliseRemainder
          (sequenceAt R (parameters approach) n)
          (remainder (sequenceAt R (parameters approach) n))

    approachNonzeroEventually :
      ∀ approach →
      Σ Nat
        (λ cutoff →
          ∀ n →
          cutoff ≤N n →
          Nonzero (sequenceAt R (parameters {R = R} approach) n))

    puncturedCongruence :
      ∀ {phi psi : Real R → Real R} →
      (∀ h → Nonzero h → phi h ≡ psi h) →
      (∀ approach →
        ConvergesTo R
          (mapSequence {R = R} limits phi (parameters {R = R} approach))
          (zero R)) →
      (∀ approach →
        ConvergesTo R
          (mapSequence {R = R} limits psi (parameters {R = R} approach))
          (zero R))

    normalizedProductCancellation :
      ∀ h q →
      Nonzero h →
      normaliseRemainder h (_*_ R h q) ≡ q

    zeroTendsToZero :
      ∀ approach →
      ConvergesTo R
        (mapSequence {R = R} limits (λ _ → zero R) (parameters {R = R} approach))
        (zero R)

open ConstructedRealPuncturedTopology public

constructedRealRemainderDerivativeStructure :
  ∀ {R : ConstructedOrderedCompleteReal} →
  (ring : ConstructedRealRingNormalisationLaws R) →
  ConstructedRealPuncturedTopology R →
  RemainderDerivativeStructure
    (ordinaryConstructiveRealMarxAlgebra {R = R} ring)
constructedRealRemainderDerivativeStructure {R} ring top = build top
  where
    build :
      ConstructedRealPuncturedTopology R →
      RemainderDerivativeStructure
        (ordinaryConstructiveRealMarxAlgebra {R = R} ring)
    build
      (record
        { limits = lim
        ; Nonzero = nz
        ; normaliseRemainder = norm
        ; normalisedAlong = normAlong
        ; normalisedAlongAt = normAlongAt
        ; approachNonzeroEventually = appNonzeroEv
        ; puncturedCongruence = congTop
        ; normalizedProductCancellation = prodCancel
        ; zeroTendsToZero = zTz
        }) =
      record
        { Nonzero = nz
        ; normaliseRemainder = norm
        ; TendsToZeroPunctured = λ phi →
            ∀ (approach : PuncturedApproach R) →
            ConvergesTo R
              (mapSequence {R = R} lim phi (parameters {R = R} approach))
              (zero R)
        ; puncturedCongruence = λ eqHyp tendPhi → congTop eqHyp tendPhi
        ; normalizedProductCancellation = prodCancel
        ; zeroTendsToZero = zTz
        }

------------------------------------------------------------------------
-- A concrete fast-Cauchy backend should inhabit these structures by
-- transporting the existing rational metric/order and quotient convergence.
