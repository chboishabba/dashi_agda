module DASHI.Physics.Motors.Resonate369SignedPitchTelescopingExact where

------------------------------------------------------------------------
-- Derived mathematical abstraction: general finite signed angular walks.
-- No vendor CAD, coordinates, switching laws or physical power claims.
-- A is an additive group of unwrapped angles (for example integer
-- millidegrees); no assumption of uniform station spacing is needed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

record AngularGroup (A : Set) : Set where
  infixl 6 _⊕_
  field
    _⊕_ : A → A → A
    zero : A
    neg : A → A
    assoc : (a b c : A) → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
    leftUnit : (a : A) → zero ⊕ a ≡ a
    rightUnit : (a : A) → a ⊕ zero ≡ a
    leftInverse : (a : A) → neg a ⊕ a ≡ zero
    rightInverse : (a : A) → a ⊕ neg a ≡ zero

module Walk {A : Set} (G : AngularGroup A) where
  open AngularGroup G

  -- Signed difference in the chosen unwrapped coordinate group.
  difference : A → A → A
  difference a b = (neg a) ⊕ b

  -- For a list of successive angle samples, sum the individual signed
  -- angular increments. The sample list may have any finite length.
  signedIncrementSum : A → List A → A
  signedIncrementSum a [] = zero
  signedIncrementSum a (b ∷ bs) =
    difference a b ⊕ signedIncrementSum b bs

  finalAngle : A → List A → A
  finalAngle a [] = a
  finalAngle a (b ∷ bs) = finalAngle b bs

  -- Cancel the first increment without assuming anything about the tail.
  cancelFirst : (a b tail : A) →
    a ⊕ (difference a b ⊕ tail) ≡ b ⊕ tail
  cancelFirst a b tail =
    trans (sym (assoc a (difference a b) tail))
      (cong (λ t → t ⊕ tail)
        (trans (sym (assoc a (neg a) b))
          (trans (cong (λ t → t ⊕ b) (rightInverse a))
            (leftUnit b))))

  -- The entire signed increment sum depends only on endpoints.
  signedPitchTelescopes : (a : A) (bs : List A) →
    a ⊕ signedIncrementSum a bs ≡ finalAngle a bs
  signedPitchTelescopes a [] = rightUnit a
  signedPitchTelescopes a (b ∷ bs) =
    trans (cancelFirst a b (signedIncrementSum b bs))
          (signedPitchTelescopes b bs)

  leftCancelToZero : (a d : A) → a ⊕ d ≡ a → d ≡ zero
  leftCancelToZero a d proof =
    trans (sym (leftUnit d))
      (trans
        (cong (λ t → t ⊕ d) (sym (leftInverse a)))
        (trans
          (assoc (neg a) a d)
          (trans
            (cong (λ t → neg a ⊕ t) proof)
            (leftInverse a))))

  -- A closed angular walk has zero net *signed unwrapped* increment.
  -- For physical circle angles this applies to a lifted walk whose end
  -- is exactly its start, not to one revolution (which ends at +360°).
  closedWalkSignedPitchZero :
    (a : A) (bs : List A) → finalAngle a bs ≡ a →
    signedIncrementSum a bs ≡ zero
  closedWalkSignedPitchZero a bs closure =
    leftCancelToZero a (signedIncrementSum a bs)
      (trans (signedPitchTelescopes a bs) closure)

  -- Relative displacement is left-translation equivariant: if d moves
  -- station a to station b, it also moves (shift+a) to (shift+b).
  rigidRotationPreservesDisplacement :
    (shift a b d : A) → a ⊕ d ≡ b →
    (shift ⊕ a) ⊕ d ≡ shift ⊕ b
  rigidRotationPreservesDisplacement shift a b d movement =
    trans (assoc shift a d) (cong (λ t → shift ⊕ t) movement)

  -- Signed closure is a separate boundary assumption; measurements
  -- must specify the unwrapped station order and terminal sample.
