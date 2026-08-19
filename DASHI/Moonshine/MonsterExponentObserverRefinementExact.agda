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
--
-- DASHI DISCIPLINE
-- Reuse DuncanSwisherTheorem12Exact through the concrete source-shaped cases in
-- DuncanSwisherMonsterExponentGeometryExact.  No second theorem carrier is
-- introduced here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.DuncanSwisherMonsterExponentGeometryExact as Geo
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Monster
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- Finite calibration index.  The support values below are not a replacement
-- for the arbitrary-prime support theorem; they are exact strictness witnesses.
------------------------------------------------------------------------

data ExponentProbe : Set where
  probe5 probe7 probe11 probe13 probe37 probe43 : ExponentProbe

supportObservation : ExponentProbe → Bool
supportObservation probe5 = true
supportObservation probe7 = true
supportObservation probe11 = true
supportObservation probe13 = true
supportObservation probe37 = false
supportObservation probe43 = false

p5Support : supportObservation probe5 ≡ true
p5Support = refl

p7Support : supportObservation probe7 ≡ true
p7Support = refl

p11Support : supportObservation probe11 ≡ true
p11Support = refl

p13Support : supportObservation probe13 ≡ true
p13Support = refl

p37NoSupport : supportObservation probe37 ≡ false
p37NoSupport = refl

p43NoSupport : supportObservation probe43 ≡ false
p43NoSupport = refl

------------------------------------------------------------------------
-- Tie the calibration labels back to the exact source-shaped theorem cases.
------------------------------------------------------------------------

p5CaseRetained : supportObservation probe5 ≡ true
p5CaseRetained with Geo.p5Case
... | _ = refl

p7CaseRetained : supportObservation probe7 ≡ true
p7CaseRetained with Geo.p7Case
... | _ = refl

p37QuadraticCaseRetained : supportObservation probe37 ≡ false
p37QuadraticCaseRetained with Geo.p37Case
... | _ = refl

p43QuadraticCaseRetained : supportObservation probe43 ≡ false
p43QuadraticCaseRetained with Geo.p43Case
... | _ = refl

------------------------------------------------------------------------
-- One coarse support fibre already contains different Monster exponents.
------------------------------------------------------------------------

p5p7SupportCollision :
  supportObservation probe5 ≡ supportObservation probe7
p5p7SupportCollision = refl

p5p7ExponentSeparated :
  Monster.monsterOrderExponent Lane.p5
  ≡ Monster.monsterOrderExponent Lane.p7 → ⊥
p5p7ExponentSeparated ()

------------------------------------------------------------------------
-- Hence no decoder from the Bool support surface can recover multiplicity on
-- even these two exact Duncan--Swisher cases.
------------------------------------------------------------------------

supportCannotDecodeMonsterExponent :
  (decode : Bool → Nat) →
  decode (supportObservation probe5) ≡ Monster.monsterOrderExponent Lane.p5 →
  decode (supportObservation probe7) ≡ Monster.monsterOrderExponent Lane.p7 →
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
  (supportObservation probe5)
  (Monster.monsterOrderExponent Lane.p5)

observeP7 : MonsterMultiplicityObservation
observeP7 = monster-multiplicity-observation
  (supportObservation probe7)
  (Monster.monsterOrderExponent Lane.p7)

forgetMultiplicity : MonsterMultiplicityObservation → Bool
forgetMultiplicity = supported

forgetP5 : forgetMultiplicity observeP5 ≡ supportObservation probe5
forgetP5 = refl

forgetP7 : forgetMultiplicity observeP7 ≡ supportObservation probe7
forgetP7 = refl

refinedObservationsDistinct : observeP5 ≡ observeP7 → ⊥
refinedObservationsDistinct ()

record MonsterExponentObserverRefinementBoundary : Set where
  field
    canonicalDuncanSwisherCasesReused : Bool
    oggSupportObserverConstructed : Bool
    quantitativeExponentObserverConstructed : Bool
    exactForgetfulMapConstructed : Bool
    sameSupportDifferentExponentWitnessConstructed : Bool
    supportDeterminesMultiplicity : Bool
    quantitativeObserverStrictlyAddsInformation : Bool

canonicalMonsterExponentObserverRefinementBoundary :
  MonsterExponentObserverRefinementBoundary
canonicalMonsterExponentObserverRefinementBoundary = record
  { canonicalDuncanSwisherCasesReused = true
  ; oggSupportObserverConstructed = true
  ; quantitativeExponentObserverConstructed = true
  ; exactForgetfulMapConstructed = true
  ; sameSupportDifferentExponentWitnessConstructed = true
  ; supportDeterminesMultiplicity = false
  ; quantitativeObserverStrictlyAddsInformation = true
  }
