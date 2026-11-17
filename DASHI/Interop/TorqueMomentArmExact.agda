{-# OPTIONS --safe #-}
module DASHI.Interop.TorqueMomentArmExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)
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

-- A citation marker is a source reference, not a proof certificate.
-- Compact results retain their exact load and a separate provenance marker.
record CitedCompactTorque : Set where
  constructor citedCompactTorque
  field
    citationMarker : String
    load : PerpendicularLoad
    compactResult : Nat
    resultExact : compactResult ≡ torqueMagnitude load

citedResultSound : (entry : CitedCompactTorque) →
  CitedCompactTorque.compactResult entry ≡
  torqueMagnitude (CitedCompactTorque.load entry)
citedResultSound = CitedCompactTorque.resultExact

makeCitedCompactTorque : String → PerpendicularLoad → CitedCompactTorque
makeCitedCompactTorque marker load =
  citedCompactTorque marker load (torqueMagnitude load) refl

compactResultPreserved : (marker : String) (load : PerpendicularLoad) →
  CitedCompactTorque.compactResult (makeCitedCompactTorque marker load) ≡
  torqueMagnitude load
compactResultPreserved marker load = refl
