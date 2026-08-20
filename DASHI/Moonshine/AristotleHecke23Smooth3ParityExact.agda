module DASHI.Moonshine.AristotleHecke23Smooth3ParityExact where

------------------------------------------------------------------------
-- UPSTREAM ARISTOTLE SOURCE / ATTRIBUTION
--
-- Aristotle (Harmonic), editor of the user-supplied Lean project.
-- Source module:
--   RequestProject.Hecke23
--   SHA-256 c433699f95c7f067c772fd9223e444869ba4e4e54907b37d4db34616572676bc
--
-- The upstream README requests @Aristotle-Harmonic attribution and the commit
-- trailer
--   Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
--
-- PRIMARY MATHEMATICAL SOURCES / CONTEXT
--
-- Jean-Pierre Serre, "A Course in Arithmetic", Springer, 1973.
-- DOI: 10.1007/978-1-4684-9884-4.
--
-- Toshitsune Miyake, "Modular Forms", Springer, 2006.
-- DOI: 10.1007/3-540-29593-3.
--
-- DASHI CONTRIBUTION
--
-- Port the source's actual Smooth3 packaging rather than leaving the earlier
-- recurrence theorem indexed only by the exponent pair.  Smooth3(n) is a
-- proof-carrying witness n = 2^i 3^j.  The source's trinity statement is then
-- literally inhabited at 3, 6 and 9.
--
-- This is intentionally finite/algebraic.  It does not add a second Hecke
-- recurrence: the coefficient uniqueness theorem remains in
-- AristotleHeckeRecurrenceCoreExact.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Nat.Base using (_^_)

record Smooth3 (n : Nat) : Set where
  constructor smooth3
  field
    twoExponent : Nat
    threeExponent : Nat
    factorisation :
      n ≡ (2 ^ twoExponent) * (3 ^ threeExponent)

open Smooth3 public

threeIsSmooth3 : Smooth3 3
threeIsSmooth3 = smooth3 0 1 refl

sixIsSmooth3 : Smooth3 6
sixIsSmooth3 = smooth3 1 1 refl

nineIsSmooth3 : Smooth3 9
nineIsSmooth3 = smooth3 0 2 refl

record TrinitySmooth3 : Set where
  constructor trinitySmooth3
  field
    three : Smooth3 3
    six : Smooth3 6
    nine : Smooth3 9

canonicalTrinitySmooth3 : TrinitySmooth3
canonicalTrinitySmooth3 =
  trinitySmooth3 threeIsSmooth3 sixIsSmooth3 nineIsSmooth3

smooth3FactorisationAtThree :
  3 ≡ (2 ^ twoExponent threeIsSmooth3)
      * (3 ^ threeExponent threeIsSmooth3)
smooth3FactorisationAtThree = factorisation threeIsSmooth3

smooth3FactorisationAtSix :
  6 ≡ (2 ^ twoExponent sixIsSmooth3)
      * (3 ^ threeExponent sixIsSmooth3)
smooth3FactorisationAtSix = factorisation sixIsSmooth3

smooth3FactorisationAtNine :
  9 ≡ (2 ^ twoExponent nineIsSmooth3)
      * (3 ^ threeExponent nineIsSmooth3)
smooth3FactorisationAtNine = factorisation nineIsSmooth3

record AristotleHecke23Smooth3Boundary : Set where
  field
    sourceSmooth3CarrierConstructed : Bool
    sourceSmooth3CarrierConstructedIsTrue :
      sourceSmooth3CarrierConstructed ≡ true
    sourceTrinitySmoothConstructed : Bool
    sourceTrinitySmoothConstructedIsTrue :
      sourceTrinitySmoothConstructed ≡ true

canonicalAristotleHecke23Smooth3Boundary : AristotleHecke23Smooth3Boundary
canonicalAristotleHecke23Smooth3Boundary = record
  { sourceSmooth3CarrierConstructed = true
  ; sourceSmooth3CarrierConstructedIsTrue = refl
  ; sourceTrinitySmoothConstructed = true
  ; sourceTrinitySmoothConstructedIsTrue = refl
  }
