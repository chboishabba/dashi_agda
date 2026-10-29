{-# OPTIONS --safe #-}
module DASHI.Interop.TorqueMomentArmExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
-- A discrete scalar moment model, not a general vector cross product.
-- Distances and perpendicular force magnitudes are represented by Nat.
-- Physical units and the sign of rotational direction are outside this model.

record PerpendicularLoad : Set where
  constructor perpendicularLoad
  field
    momentArm : Nat
    perpendicularForce : Nat

torqueMagnitude : PerpendicularLoad → Nat
torqueMagnitude load =
  PerpendicularLoad.momentArm load * PerpendicularLoad.perpendicularForce load

record EqualPerpendicularLoads : Set where
  constructor equalPerpendicularLoads
  field
    first : PerpendicularLoad
    second : PerpendicularLoad
    sameArm : PerpendicularLoad.momentArm first ≡ PerpendicularLoad.momentArm second
    sameForce : PerpendicularLoad.perpendicularForce first ≡ PerpendicularLoad.perpendicularForce second

equalLoadsEqualTorque : (loads : EqualPerpendicularLoads) →
  torqueMagnitude (EqualPerpendicularLoads.first loads) ≡
  torqueMagnitude (EqualPerpendicularLoads.second loads)
equalLoadsEqualTorque (equalPerpendicularLoads first second refl refl) = refl

zeroArmZeroTorque : (force : Nat) →
  torqueMagnitude (perpendicularLoad 0 force) ≡ 0
zeroArmZeroTorque force = refl

zeroForceZeroTorque : (arm : Nat) →
  torqueMagnitude (perpendicularLoad arm 0) ≡ 0
zeroForceZeroTorque arm = refl
