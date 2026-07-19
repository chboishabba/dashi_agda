{-# OPTIONS --safe #-}

module DASHI.Geometry.QuadraticForcingGate where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Geometry.UniversalCanonicalQuotient
open import DASHI.Geometry.HilbertLorentzForcing

------------------------------------------------------------------------
-- Minimal closure gate.
--
-- The ultrametric/contraction layer is represented here by its completed
-- output: a canonical quotient presentation.  The gate does not claim that
-- contraction alone creates a quadratic form.  It requires a Hilbert lift and
-- a one-dimensional invariant quadratic ray, then uses spatial isotropy,
-- finite-speed null-cone structure, and time orientation to force (3,1).
------------------------------------------------------------------------

record QuadraticForcingPremises
  {X Quot : Set}
  (P : QuotientPresentation X Quot)
  : Set₁ where
  field
    hilbert : HilbertLift
    symmetry : LinearAction hilbert
    invariantRay : UniqueInvariantQuadraticRay hilbert symmetry

    isotropyNormalForm :
      SpatialIsotropyNormalForm hilbert
        (UniqueInvariantQuadraticRay.distinguished invariantRay)

    finiteSpeed : FiniteSpeedNullCone isotropyNormalForm
    timeOrientation : FutureTimeOrientation isotropyNormalForm

open QuadraticForcingPremises public

record QuadraticForcingConclusion
  {X Quot : Set}
  (P : QuotientPresentation X Quot)
  (A : QuadraticForcingPremises P)
  : Set₁ where
  field
    invariantQuadratic : Quadratic (hilbert A)
    invariantQuadratic-is-distinguished :
      invariantQuadratic ≡
      UniqueInvariantQuadraticRay.distinguished (invariantRay A)

    invariantQuadraticUniqueUpToScale :
      UniqueInvariantQuadraticRay (hilbert A) (symmetry A)

    lorentzSignature : LorentzSignature
    lorentzSignature-forced :
      lorentzSignature ≡
      isotropy-finiteSpeed-forces-lorentz
        (isotropyNormalForm A)
        (finiteSpeed A)

    signature31-forced : lorentzSignature ≡ signature31

open QuadraticForcingConclusion public

quadraticForcingGate :
  ∀ {X Quot : Set}
  (P : QuotientPresentation X Quot) →
  (A : QuadraticForcingPremises P) →
  QuadraticForcingConclusion P A
quadraticForcingGate P A = record
  { invariantQuadratic =
      UniqueInvariantQuadraticRay.distinguished (invariantRay A)
  ; invariantQuadratic-is-distinguished =
      Agda.Builtin.Equality.refl
  ; invariantQuadraticUniqueUpToScale = invariantRay A
  ; lorentzSignature =
      isotropy-finiteSpeed-forces-lorentz
        (isotropyNormalForm A)
        (finiteSpeed A)
  ; lorentzSignature-forced = Agda.Builtin.Equality.refl
  ; signature31-forced =
      orientation-selects-31
        (isotropyNormalForm A)
        (finiteSpeed A)
        (timeOrientation A)
  }

------------------------------------------------------------------------
-- The quotient side of the gate: every invariant observable descends uniquely
-- to the canonical state space.  This is the exact universal property needed
-- for orbit/gauge-independent physics observables.
------------------------------------------------------------------------

observable-descends-uniquely :
  ∀ {X Quot Y : Set}
  (P : QuotientPresentation X Quot)
  (observable : X → Y) →
  Invariant P observable →
  UniqueFactorisation (π P) observable
observable-descends-uniquely = universalCanonicalQuotient
