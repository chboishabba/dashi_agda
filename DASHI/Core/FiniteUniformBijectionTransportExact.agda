module DASHI.Core.FiniteUniformBijectionTransportExact where

------------------------------------------------------------------------
-- EXACT UNIFORM-MASS TRANSPORT ALONG AN EXPLICIT BIJECTION
--
-- No division or real probability is required.  A source carrier has an exact
-- Nat-valued mass that is constant at every point.  Pulling that mass through
-- a proved two-sided bijection gives an exactly uniform target carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

record ExplicitBijection (A B : Set) : Set₁ where
  field
    to : A → B
    from : B → A
    fromTo : (a : A) → from (to a) ≡ a
    toFrom : (b : B) → to (from b) ≡ b

open ExplicitBijection public

record UniformNatMass (A : Set) : Set₁ where
  field
    mass : A → Nat
    commonMass : Nat
    uniform : (a : A) → mass a ≡ commonMass

open UniformNatMass public

transportUniformMass :
  {A B : Set} →
  ExplicitBijection A B →
  UniformNatMass A →
  UniformNatMass B
transportUniformMass bij source = record
  { mass = λ b → mass source (from bij b)
  ; commonMass = commonMass source
  ; uniform = λ b → uniform source (from bij b)
  }

unitMass : (A : Set) → UniformNatMass A
unitMass A = record
  { mass = λ _ → 1
  ; commonMass = 1
  ; uniform = λ _ → refl
  }

transportUnitMass :
  {A B : Set} →
  ExplicitBijection A B →
  UniformNatMass B
transportUnitMass {A} bij = transportUniformMass bij (unitMass A)

record UniformBijectionBoundary : Set where
  constructor uniformBijectionBoundary
  field
    forwardMapAloneSuffices : Nat
    reverseMapRequired : Nat
    twoInverseLawsRequired : Nat
    realDivisionRequired : Nat
    exactNatMassTransportOwned : Nat

canonicalUniformBijectionBoundary : UniformBijectionBoundary
canonicalUniformBijectionBoundary =
  uniformBijectionBoundary 0 1 1 0 1
