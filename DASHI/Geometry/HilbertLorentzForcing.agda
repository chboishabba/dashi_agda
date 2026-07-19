{-# OPTIONS --safe #-}

module DASHI.Geometry.HilbertLorentzForcing where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Minimal Hilbert-like carrier.
--
-- The forcing theorem below does not pretend that an ultrametric is already
-- an inner-product metric.  A Hilbert lift is supplied explicitly, together
-- with the laws needed by the concrete instance.
------------------------------------------------------------------------

record HilbertLift : Set₁ where
  field
    Vector : Set
    Scalar : Set
    zero : Vector
    _+_ : Vector → Vector → Vector
    _·_ : Scalar → Vector → Vector
    ⟪_,_⟫ : Vector → Vector → Scalar

open HilbertLift public

Quadratic : HilbertLift → Set
Quadratic H = Vector H → Scalar H

record LinearAction (H : HilbertLift) : Set₁ where
  field
    Group : Set
    act : Group → Vector H → Vector H

open LinearAction public

InvariantQuadratic :
  ∀ {H : HilbertLift} → LinearAction H → Quadratic H → Set
InvariantQuadratic A Q = ∀ g x → Q (act A g x) ≡ Q x

------------------------------------------------------------------------
-- Uniqueness of the invariant quadratic is a representation-theoretic gate.
-- In a concrete development this is normally discharged by irreducibility
-- (with the appropriate real/complex/quaternionic commutant hypothesis).
------------------------------------------------------------------------

record UniqueInvariantQuadraticRay
  (H : HilbertLift)
  (A : LinearAction H)
  : Set₁ where
  field
    distinguished : Quadratic H
    distinguished-invariant : InvariantQuadratic A distinguished

    scale : Quadratic H → Scalar H
    unique-up-to-scale :
      ∀ (Q : Quadratic H) →
      InvariantQuadratic A Q →
      ∀ x → Q x ≡ scale Q · distinguished x

open UniqueInvariantQuadraticRay public

------------------------------------------------------------------------
-- Spatial isotropy removes time-space cross terms and forces one repeated
-- coefficient on the spatial block.  We record only the normal-form data
-- consumed by signature forcing; a concrete representation module must prove
-- this record from its rotation action.
------------------------------------------------------------------------

data Sign : Set where
  positive : Sign
  negative : Sign

data Opposite : Sign → Sign → Set where
  positive-negative : Opposite positive negative
  negative-positive : Opposite negative positive

record SpatialIsotropyNormalForm
  (H : HilbertLift)
  (Q : Quadratic H)
  : Set₁ where
  field
    timeSign : Sign
    spaceSign : Sign
    spatialMultiplicity : Nat
    spatialMultiplicity-is-three : spatialMultiplicity ≡ 3

open SpatialIsotropyNormalForm public

------------------------------------------------------------------------
-- Finite speed must be stronger than mere locality.  The required premise is
-- the existence of a nontrivial preserved null boundary, which rules out a
-- definite quadratic and forces opposite signs between time and space.
------------------------------------------------------------------------

record FiniteSpeedNullCone
  {H : HilbertLift}
  {Q : Quadratic H}
  (N : SpatialIsotropyNormalForm H Q)
  : Set₁ where
  field
    oppositeSigns : Opposite (timeSign N) (spaceSign N)

open FiniteSpeedNullCone public

data LorentzSignature : Set where
  signature31 : LorentzSignature
  signature13 : LorentzSignature

opposite-forces-lorentz :
  ∀ {t s : Sign} → Opposite t s → LorentzSignature
opposite-forces-lorentz positive-negative = signature31
opposite-forces-lorentz negative-positive = signature13

isotropy-finiteSpeed-forces-lorentz :
  ∀ {H : HilbertLift}
  {Q : Quadratic H}
  (N : SpatialIsotropyNormalForm H Q) →
  FiniteSpeedNullCone N →
  LorentzSignature
isotropy-finiteSpeed-forces-lorentz N F =
  opposite-forces-lorentz (oppositeSigns F)

------------------------------------------------------------------------
-- Time orientation selects the sign convention after Lorentzianity has been
-- forced.  It does not create indefiniteness.
------------------------------------------------------------------------

record FutureTimeOrientation
  {H : HilbertLift}
  {Q : Quadratic H}
  (N : SpatialIsotropyNormalForm H Q)
  : Set₁ where
  field
    future-time-positive : timeSign N ≡ positive

open FutureTimeOrientation public

orientation-selects-31 :
  ∀ {H : HilbertLift}
  {Q : Quadratic H}
  (N : SpatialIsotropyNormalForm H Q) →
  (F : FiniteSpeedNullCone N) →
  FutureTimeOrientation N →
  isotropy-finiteSpeed-forces-lorentz N F ≡ signature31
orientation-selects-31 N F O
  with timeSign N | spaceSign N | oppositeSigns F | future-time-positive O
... | positive | negative | positive-negative | refl = refl
