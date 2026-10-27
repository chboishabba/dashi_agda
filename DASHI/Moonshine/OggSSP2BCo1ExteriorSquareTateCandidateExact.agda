module DASHI.Moonshine.OggSSP2BCo1ExteriorSquareTateCandidateExact where

------------------------------------------------------------------------
-- 2B MODULAR-MOONSHINE / Co1 EXTERIOR-SQUARE CANDIDATE
--
-- Source facts:
--   * the characteristic-two 2B modular-moonshine object is acted on by
--       2^24.Co1;
--   * the original Borcherds--Ryba discussion explicitly did not prove that
--       the normal 2^24 acts trivially;
--   * Co1 has a 24-dimensional irreducible GF(2) module;
--   * its exterior square has dimension 276 and composition data beginning
--       with trivial / 274-dimensional structure in characteristic two.
--
-- DASHI tests, rather than assumes, the candidate:
--   Tate weight-two 276  ?=  wedge^2(Co1-24).
--
-- The GAP screen constructs the actual Atlas Co1 24d GF2 matrices, forms the
-- full 276d exterior-square matrices, and computes radical/socle/endomorphism/
-- composition-series data.  A separate probe asks what explicit char-2 data
-- AtlasRep exposes for 2^24.Co1.
--
-- Firewalls:
--   no triviality of the normal 2^24 is asserted here;
--   no Tate<->exterior-square same-object identification is asserted here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)

co1NaturalDimension : Nat
co1NaturalDimension = 24

co1ExteriorSquareDimension : Nat
co1ExteriorSquareDimension = 276

pairCount24 : Nat
pairCount24 = 276

pairCountIs276 : pairCount24 ≡ 276
pairCountIs276 = refl

record Co1ExteriorSquareCandidateStatus : Set where
  constructor co1-exterior-square-candidate-status
  field
    modularMoonshineGroup2Pow24Co1Sourced : Bool
    normal2Pow24TrivialityHistoricallyUnproved : Bool
    co1Natural24GF2Sourced : Bool
    exteriorSquareDimension276Exact : Bool
    exteriorSquareRuntimeFingerprintScreenImplemented : Bool
    atlas2Pow24Co1Char2ProbeImplemented : Bool
    normal2Pow24ActsTriviallyOnWeightTwoTatePaid : Bool
    actualTate276IsCo1ExteriorSquarePaid : Bool
    nextTest : String

canonicalCo1ExteriorSquareCandidateStatus : Co1ExteriorSquareCandidateStatus
canonicalCo1ExteriorSquareCandidateStatus =
  co1-exterior-square-candidate-status
    true true true true true true
    false false
    "Run the Co1 wedge^2(24) and 2^24.Co1 char-2 probes; then compute whether the normal 2^24 acts trivially on the actual weight-two Tate head. Only after that compare the full extension fingerprint with the duad/Co1 276 candidate."

normal2Pow24TrivialityStillOpen :
  Co1ExteriorSquareCandidateStatus.normal2Pow24ActsTriviallyOnWeightTwoTatePaid
    canonicalCo1ExteriorSquareCandidateStatus
  ≡ false
normal2Pow24TrivialityStillOpen = refl

sameObjectExteriorSquareStillOpen :
  Co1ExteriorSquareCandidateStatus.actualTate276IsCo1ExteriorSquarePaid
    canonicalCo1ExteriorSquareCandidateStatus
  ≡ false
sameObjectExteriorSquareStillOpen = refl
