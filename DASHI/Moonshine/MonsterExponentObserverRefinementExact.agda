module DASHI.Moonshine.MonsterExponentObserverRefinementExact where

------------------------------------------------------------------------
-- CROSS-POLLINATION CONTEXT
--
-- The observer-refinement programme in PR #584 distinguishes a coarse surface
-- from a strictly richer observation whenever one coarse fibre contains states
-- separated by the richer observer.
--
-- Here the coarse observation is only Duncan--Swisher/Ogg support:
--
--   support(p) = "quadratic supersingular locus empty".
--
-- The richer observation retains the actual Monster exponent v_p(|M|).
-- Duncan--Swisher Theorem 1.2 shows geometrically why the refinement is real:
-- among support-positive primes the rational-locus regime and minimum FULL
-- automorphism order still vary.
--
-- PRIMARY SOURCE
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.DuncanSwisherSupersingularExponentDatumExact as DS
import DASHI.Moonshine.DuncanSwisherMonsterExponentGeometryExact as Geo
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Monster
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- Coarse support observer.
------------------------------------------------------------------------

supportObservation : DS.SupersingularExponentGeometry → Bool
supportObservation G with DS.regime G
... | DS.singletonRationalNoQuadratic = true
... | DS.multipleRationalNoQuadratic = true
... | DS.quadraticLocusPresent = false

p5Support : supportObservation Geo.p5Geometry ≡ true
p5Support = refl

p7Support : supportObservation Geo.p7Geometry ≡ true
p7Support = refl

p11Support : supportObservation Geo.p11Geometry ≡ true
p11Support = refl

p13Support : supportObservation Geo.p13Geometry ≡ true
p13Support = refl

p37NoSupport : supportObservation Geo.p37Geometry ≡ false
p37NoSupport = refl

p43NoSupport : supportObservation Geo.p43Geometry ≡ false
p43NoSupport = refl

------------------------------------------------------------------------
-- One coarse support fibre already contains different Monster exponents.
------------------------------------------------------------------------

p5p7SupportCollision :
  supportObservation Geo.p5Geometry ≡ supportObservation Geo.p7Geometry
p5p7SupportCollision = refl

p5p7ExponentSeparated :
  Monster.monsterOrderExponent Lane.p5
  ≡ Monster.monsterOrderExponent Lane.p7 → ⊥
p5p7ExponentSeparated ()

------------------------------------------------------------------------
-- Hence no decoder from the Bool support surface can recover multiplicity on
-- even these two source-certified cases.
------------------------------------------------------------------------

supportCannotDecodeMonsterExponent :
  (decode : Bool → Nat) →
  decode (supportObservation Geo.p5Geometry) ≡ Monster.monsterOrderExponent Lane.p5 →
  decode (supportObservation Geo.p7Geometry) ≡ Monster.monsterOrderExponent Lane.p7 →
  ⊥
supportCannotDecodeMonsterExponent decode p5Exact p7Exact =
  p5p7ExponentSeparated (trans (sym p5Exact) p7Exact)

------------------------------------------------------------------------
-- Explicit refined observation: support plus exponent.
------------------------------------------------------------------------

record MonsterMultiplicityObservation : Set where
  constructor monster-multiplicity-observation
  field
    supported : Bool
    exponent : Nat

open MonsterMultiplicityObservation public

observeP5 : MonsterMultiplicityObservation
observeP5 = monster-multiplicity-observation
  (supportObservation Geo.p5Geometry)
  (Monster.monsterOrderExponent Lane.p5)

observeP7 : MonsterMultiplicityObservation
observeP7 = monster-multiplicity-observation
  (supportObservation Geo.p7Geometry)
  (Monster.monsterOrderExponent Lane.p7)

forgetMultiplicity : MonsterMultiplicityObservation → Bool
forgetMultiplicity = supported

forgetP5 : forgetMultiplicity observeP5 ≡ supportObservation Geo.p5Geometry
forgetP5 = refl

forgetP7 : forgetMultiplicity observeP7 ≡ supportObservation Geo.p7Geometry
forgetP7 = refl

refinedObservationsDistinct : observeP5 ≡ observeP7 → ⊥
refinedObservationsDistinct ()

record MonsterExponentObserverRefinementBoundary : Set where
  field
    oggSupportObserverConstructed : Bool
    quantitativeExponentObserverConstructed : Bool
    exactForgetfulMapConstructed : Bool
    sameSupportDifferentExponentWitnessConstructed : Bool
    supportDeterminesMultiplicity : Bool
    quantitativeObserverStrictlyAddsInformation : Bool

canonicalMonsterExponentObserverRefinementBoundary :
  MonsterExponentObserverRefinementBoundary
canonicalMonsterExponentObserverRefinementBoundary = record
  { oggSupportObserverConstructed = true
  ; quantitativeExponentObserverConstructed = true
  ; exactForgetfulMapConstructed = true
  ; sameSupportDifferentExponentWitnessConstructed = true
  ; supportDeterminesMultiplicity = false
  ; quantitativeObserverStrictlyAddsInformation = true
  }
