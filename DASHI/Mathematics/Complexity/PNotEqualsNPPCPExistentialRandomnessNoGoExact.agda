module DASHI.Mathematics.Complexity.PNotEqualsNPPCPExistentialRandomnessNoGoExact where

------------------------------------------------------------------------
-- PCP / RANDOMIZED VERIFICATION SANITY NO-GO
--
-- PCP-style verification can inspect only a few proof locations, but its
-- soundness is probabilistic over verifier randomness.
--
-- An ordinary SAT witness is existential.  Therefore the naive translation
--
--   "guess proof bits AND guess verifier randomness"
--
-- is unsound: a false statement may have some accepting random seeds even
-- though a nonzero fraction of seeds reject every proof.
--
-- This owner proves that logical mismatch constructively, then records the
-- cost of the simplest deterministic repair: universally enumerate all r-bit
-- random seeds.  The branch count is exactly 2^r.
--
-- Attribution/calibration:
--   Arora--Safra, JACM 45(1), 1998, DOI 10.1145/273865.273901.
--   Arora--Lund--Motwani--Sudan--Szegedy, JACM 45(3), 1998,
--   DOI 10.1145/278298.278306.
--
-- No PCP theorem is imported as a P != NP proof.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Product using (Σ; _,_)
open import Data.Vec.Base using (Vec; []; _∷_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPDiagonalizationSourceAtlasExact as Sources

------------------------------------------------------------------------
-- Existential and universal use of verifier randomness.
------------------------------------------------------------------------

AcceptingRandomSeed :
  ∀ {Proof : Set} {randomBits : Nat} →
  (Proof → Vec Bool randomBits → Bool) →
  Proof →
  Set
AcceptingRandomSeed verifier proof =
  Σ (Vec Bool _) λ randomSeed →
    verifier proof randomSeed ≡ true

RejectingRandomSeed :
  ∀ {Proof : Set} {randomBits : Nat} →
  (Proof → Vec Bool randomBits → Bool) →
  Proof →
  Set
RejectingRandomSeed verifier proof =
  Σ (Vec Bool _) λ randomSeed →
    verifier proof randomSeed ≡ false

AllRandomSeedsAccept :
  ∀ {Proof : Set} {randomBits : Nat} →
  (Proof → Vec Bool randomBits → Bool) →
  Proof →
  Set
AllRandomSeedsAccept verifier proof =
  (randomSeed : Vec Bool _) →
  verifier proof randomSeed ≡ true

------------------------------------------------------------------------
-- One-bit toy verifier:
--
--   seed=false -> accept
--   seed=true  -> reject
--
-- for every proof.  Hence:
--   * every proof has an accepting seed;
--   * every proof also has a rejecting seed.
--
-- This is exactly enough to show that existentially guessing randomness does
-- not preserve randomized soundness.
------------------------------------------------------------------------

oneBitVerifier :
  ∀ {Proof : Set} →
  Proof →
  Vec Bool (suc zero) →
  Bool
oneBitVerifier proof (false ∷ []) =
  true
oneBitVerifier proof (true ∷ []) =
  false

oneBitVerifierHasAcceptingSeed :
  ∀ {Proof : Set}
    (proof : Proof) →
  AcceptingRandomSeed oneBitVerifier proof
oneBitVerifierHasAcceptingSeed proof =
  (false ∷ []) , refl

oneBitVerifierHasRejectingSeed :
  ∀ {Proof : Set}
    (proof : Proof) →
  RejectingRandomSeed oneBitVerifier proof
oneBitVerifierHasRejectingSeed proof =
  (true ∷ []) , refl

record FalseInstanceRandomizedSoundnessToy : Set₁ where
  field
    Proof : Set
    proof : Proof

    -- Minimal logical shadow of soundness below one:
    -- a rejecting seed exists for the alleged false instance.
    rejectingRandomnessExists :
      RejectingRandomSeed oneBitVerifier proof

    -- Yet existential SAT-style randomness still finds acceptance.
    existentialRandomnessStillAccepts :
      AcceptingRandomSeed oneBitVerifier proof

canonicalFalseInstanceRandomizedSoundnessToy :
  FalseInstanceRandomizedSoundnessToy
canonicalFalseInstanceRandomizedSoundnessToy = record
  { Proof = Bool
  ; proof = false
  ; rejectingRandomnessExists =
      oneBitVerifierHasRejectingSeed false
  ; existentialRandomnessStillAccepts =
      oneBitVerifierHasAcceptingSeed false
  }

------------------------------------------------------------------------
-- Deterministic universalization over all random seeds.
------------------------------------------------------------------------

allSeedsAcceptBool :
  ∀ {Proof : Set}
    (randomBits : Nat) →
  (Proof → Vec Bool randomBits → Bool) →
  Proof →
  Bool
allSeedsAcceptBool zero verifier proof =
  verifier proof []
allSeedsAcceptBool (suc randomBits) verifier proof =
  Cook.andBool
    (allSeedsAcceptBool
      randomBits
      (λ proof tail →
        verifier proof (false ∷ tail))
      proof)
    (allSeedsAcceptBool
      randomBits
      (λ proof tail →
        verifier proof (true ∷ tail))
      proof)

------------------------------------------------------------------------
-- Naive branch-count accounting: checking every seed requires 2^r verifier
-- leaves.
------------------------------------------------------------------------

pow2 : Nat → Nat
pow2 zero =
  suc zero
pow2 (suc exponent) =
  pow2 exponent + pow2 exponent

universalSeedLeafChecks : Nat → Nat
universalSeedLeafChecks zero =
  suc zero
universalSeedLeafChecks (suc randomBits) =
  universalSeedLeafChecks randomBits
  +
  universalSeedLeafChecks randomBits

universalSeedLeafChecksExact :
  (randomBits : Nat) →
  universalSeedLeafChecks randomBits
  ≡ pow2 randomBits
universalSeedLeafChecksExact zero =
  refl
universalSeedLeafChecksExact (suc randomBits)
    rewrite universalSeedLeafChecksExact randomBits =
  refl

------------------------------------------------------------------------
-- Universal checking repairs the one-bit toy.
------------------------------------------------------------------------

oneBitUniversalCheckRejects :
  ∀ {Proof : Set}
    (proof : Proof) →
  allSeedsAcceptBool
    (suc zero)
    oneBitVerifier
    proof
  ≡ false
oneBitUniversalCheckRejects proof =
  refl

------------------------------------------------------------------------
-- Consequence for the self-diagonal route.
--
-- PCP-style few-query verification does not directly give an existential SAT
-- certificate for exact circuit evaluation.  Existentially quantifying the
-- verifier randomness loses soundness; naively universalizing r random bits
-- expands to 2^r verifier branches.
--
-- A successful PCP cross-pollination therefore needs an additional
-- derandomization/universalization or algebraic consistency mechanism whose
-- own syntax/resource cost closes the diagonal size recurrence.
------------------------------------------------------------------------
