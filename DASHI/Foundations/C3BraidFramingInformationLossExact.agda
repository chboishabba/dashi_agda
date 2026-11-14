module DASHI.Foundations.C3BraidFramingInformationLossExact where

-- The minimal injectivity counterexample: same observed strand endpoints,
-- distinct framing counters. A full physical framed braid needs Z-valued
-- winding, not just a binary orientation sign or a 27-state voxel.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

import DASHI.Foundations.C3NineSiteAlternatingOrbitExact as Orbit
import DASHI.Foundations.C3BraidEndpointMobiusExact as Orient

record FramedEndpoint : Set where
  constructor framed
  field
    position : Orbit.Site
    localOrientation : Orient.EndpointOrientation
    fullTurns : Nat
open FramedEndpoint public

record BareEndpoint : Set where
  constructor bare
  field
    position : Orbit.Site
    localOrientation : Orient.EndpointOrientation
open BareEndpoint public

forgetFraming : FramedEndpoint → BareEndpoint
forgetFraming (framed p o n) = bare p o

untwisted : FramedEndpoint
untwisted = framed Orbit.TL Orient.forward zero

oneFullTurn : FramedEndpoint
oneFullTurn = framed Orbit.TL Orient.forward (suc zero)

sameEndpoint : forgetFraming untwisted ≡ forgetFraming oneFullTurn
sameEndpoint = refl

zeroNotSuc : zero ≡ suc zero → ⊥
zeroNotSuc ()

differentFraming : untwisted ≡ oneFullTurn → ⊥
differentFraming eq = zeroNotSuc (cong fullTurns eq)

