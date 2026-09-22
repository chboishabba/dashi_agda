module DASHI.Analysis.ConstructiveRealToStandardRealExact where

------------------------------------------------------------------------
-- GENERIC SETOID CONSTRUCTIVE REAL -> STANDARD REAL INTERPRETATION
--
-- Application-neutral owner for the cross-prover real seam.
--
-- The source is the repo's existing quotient-free setoid real backend.
-- The target is an abstract standard real/transcendental algebra.  A transport
-- interpretation must respect source extensional equality and preserve exactly
-- the operations required by analytic consumers.
--
-- Raw-representative injectivity is intentionally absent.  Optional same-object
-- faithfulness is isolated in a separate record.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ)

import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine

------------------------------------------------------------------------
-- Source transcendental extension of the existing setoid real spine.
------------------------------------------------------------------------

record SetoidRealTranscendental
    (R : Spine.SetoidOrderedCompleteReal) : Set₁ where
  field
    exp sin cos : Spine.Carrier R → Spine.Carrier R
    pi : Spine.Carrier R

    expCong :
      ∀ {x y} →
      Spine._≈_ R x y →
      Spine._≈_ R (exp x) (exp y)

    sinCong :
      ∀ {x y} →
      Spine._≈_ R x y →
      Spine._≈_ R (sin x) (sin y)

    cosCong :
      ∀ {x y} →
      Spine._≈_ R x y →
      Spine._≈_ R (cos x) (cos y)

open SetoidRealTranscendental public

------------------------------------------------------------------------
-- Abstract target standard-real algebra.
------------------------------------------------------------------------

record StandardRealTranscendental : Set₁ where
  field
    Carrier : Set

    zero one pi : Carrier
    add sub mul : Carrier → Carrier → Carrier
    neg : Carrier → Carrier

    exp sin cos : Carrier → Carrier

open StandardRealTranscendental public

------------------------------------------------------------------------
-- Primitive interpretation.
------------------------------------------------------------------------

record StandardRealInterpretation
    (R : Spine.SetoidOrderedCompleteReal)
    (A : SetoidRealTranscendental R)
    (T : StandardRealTranscendental) : Set₁ where

  field
    mapR : Spine.Carrier R → Carrier T

    respectsEquivalent :
      ∀ {x y} →
      Spine._≈_ R x y →
      mapR x ≡ mapR y

    preservesZero :
      mapR (Spine.zero R) ≡ zero T

    preservesOne :
      mapR (Spine.one R) ≡ one T

    preservesAdd :
      ∀ x y →
      mapR (Spine._+_ R x y)
      ≡ add T (mapR x) (mapR y)

    preservesSub :
      ∀ x y →
      mapR (Spine._-_ R x y)
      ≡ sub T (mapR x) (mapR y)

    preservesMul :
      ∀ x y →
      mapR (Spine._*_ R x y)
      ≡ mul T (mapR x) (mapR y)

    preservesNeg :
      ∀ x →
      mapR (Spine.neg R x)
      ≡ neg T (mapR x)

    preservesExp :
      ∀ x →
      mapR (SetoidRealTranscendental.exp A x)
      ≡ StandardRealTranscendental.exp T (mapR x)

    preservesSin :
      ∀ x →
      mapR (SetoidRealTranscendental.sin A x)
      ≡ StandardRealTranscendental.sin T (mapR x)

    preservesCos :
      ∀ x →
      mapR (SetoidRealTranscendental.cos A x)
      ≡ StandardRealTranscendental.cos T (mapR x)

    preservesPi :
      mapR (SetoidRealTranscendental.pi A)
      ≡ StandardRealTranscendental.pi T

open StandardRealInterpretation public

------------------------------------------------------------------------
-- Optional same-object faithfulness; not required for ordinary transport.
------------------------------------------------------------------------

record FaithfulStandardRealInterpretation
    {R : Spine.SetoidOrderedCompleteReal}
    {A : SetoidRealTranscendental R}
    {T : StandardRealTranscendental}
    (I : StandardRealInterpretation R A T) : Set₁ where

  field
    reflectsEquivalent :
      ∀ {x y} →
      mapR I x ≡ mapR I y →
      Spine._≈_ R x y

open FaithfulStandardRealInterpretation public

------------------------------------------------------------------------
-- Componentwise complex carrier and induced transport.
------------------------------------------------------------------------

record StandardComplex
    (T : StandardRealTranscendental) : Set where
  constructor complex
  field
    re im : Carrier T

open StandardComplex public

mapComplex :
  ∀ {R A T} →
  StandardRealInterpretation R A T →
  Spine.Carrier R →
  Spine.Carrier R →
  StandardComplex T
mapComplex I x y =
  complex (mapR I x) (mapR I y)

mapComplexEquivalent :
  ∀ {R A T}
    (I : StandardRealInterpretation R A T)
    {xr xi yr yi} →
  Spine._≈_ R xr yr →
  Spine._≈_ R xi yi →
  mapComplex I xr xi ≡ mapComplex I yr yi
mapComplexEquivalent I hx hy
  rewrite respectsEquivalent I hx
        | respectsEquivalent I hy =
  refl

------------------------------------------------------------------------
-- Boundary status: this file owns the reusable contract, not its cross-prover
-- inhabitant.
------------------------------------------------------------------------

record ConstructiveRealToStandardRealBoundary : Set where
  constructor boundary
  field
    setoidRespectRequired : Bool
    rawRepresentativeInjectivityRequired : Bool
    faithfulnessSeparatedFromTransport : Bool

canonicalBoundary : ConstructiveRealToStandardRealBoundary
canonicalBoundary =
  boundary true false true

