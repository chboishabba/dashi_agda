module DASHI.Crypto.MLKEMNTTActualCBD2EightCoefficientLeakageResolutionExact where

------------------------------------------------------------------------
-- ML-KEM / FIPS-203: EIGHT-COEFFICIENT CBD2 LEAKAGE-RESOLUTION PROFILE
--
-- Primary cryptographic source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Defensive side-channel context (not proof inputs):
-- Mike Hamburg, Julius Hermelink, Robert Primas, Simona Samardjiska,
-- Thomas Schamberger, Silvan Streit, Emanuele Strieder,
-- Christine van Vredendaal,
-- "Chosen Ciphertext k-Trace Attacks on Masked CCA2 Secure Kyber",
-- IACR Transactions on Cryptographic Hardware and Embedded Systems 2021(4),
-- 88--113. DOI: 10.46586/tches.v2021.i4.88-113.
--
-- Estuardo Alpirez Bock, Gustavo Banegas, Chris Brzuska,
-- Lukasz Chmielewski, Kirthivaasan Puniamurthy, Milan Sorf,
-- "Breaking DPA-Protected Kyber via the Pair-Pointwise Multiplication",
-- ACNS 2024, LNCS 14584, 101--130.
-- DOI: 10.1007/978-3-031-54773-7_5.
--
-- PURPOSE
-- -------
-- Record the exact arithmetic consequences of the source-faithful exhaustive
-- m=8 CBD2 enumeration performed by
--
--   scripts/crypto_ntt_cbd_block_reconciliation_probe.py
--
-- on the complete 5^8 = 390625 coefficient carrier.  The three actual FIPS
-- residue-pair profiles currently pinned by that script are:
--
--   (0,1): images 271441, collision pairs 151632,
--          conditional mass 693889, max fibre 4;
--   (0,2): images 369865, collision pairs 20805,
--          conditional mass 432235, max fibre 3;
--   (0,3): images 390625, collision pairs 0,
--          conditional mass 390625, max fibre 1.
--
-- For a finite map with fibre sizes c_y,
--
--   sum_y c_y^2 = N + 2 * sum_y choose(c_y,2).
--
-- Hence the reported conditional masses are forced by candidate count and
-- unordered-collision count.  This module kernel-checks that arithmetic and
-- packages the defensive interpretation boundary.
--
-- IMPORTANT BLUE-TEAM BOUNDARY
-- ----------------------------
-- The raw (0,3) enumeration is collision-free on this conditioned eight-
-- coefficient carrier.  That is a leakage-sensitivity finding: if an actual
-- implementation observation preserves enough of this raw pair, ambiguity can
-- collapse sharply.  It is NOT a theorem that a real trace exposes the raw pair,
-- not a whole-polynomial/key recovery theorem, and not a runtime claim.
-- An actual side-channel observation is normally a coarsening (Hamming weight,
-- timing bucket, masked share, etc.), and raw injectivity does not imply that the
-- coarsened observation is injective.  A concrete observation-channel theorem is
-- therefore mandatory before any implementation claim.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Exhaustive-enumeration profile carrier.
------------------------------------------------------------------------

record LeakageResolutionProfile : Set where
  constructor leakage-resolution-profile
  field
    candidates : Nat
    images : Nat
    collisionPairs : Nat
    conditionalMass : Nat
    maxFibre : Nat

open LeakageResolutionProfile public

pair01 : LeakageResolutionProfile
pair01 = leakage-resolution-profile 390625 271441 151632 693889 4

pair02 : LeakageResolutionProfile
pair02 = leakage-resolution-profile 390625 369865 20805 432235 3

pair03 : LeakageResolutionProfile
pair03 = leakage-resolution-profile 390625 390625 0 390625 1

pair01CandidateCount : candidates pair01 ≡ 390625
pair01CandidateCount = refl

pair02CandidateCount : candidates pair02 ≡ 390625
pair02CandidateCount = refl

pair03CandidateCount : candidates pair03 ≡ 390625
pair03CandidateCount = refl

------------------------------------------------------------------------
-- Exact finite-list-mass arithmetic.
------------------------------------------------------------------------

pair01MassFromCollisionPairs :
  conditionalMass pair01 ≡ candidates pair01 + 2 * collisionPairs pair01
pair01MassFromCollisionPairs = refl

pair02MassFromCollisionPairs :
  conditionalMass pair02 ≡ candidates pair02 + 2 * collisionPairs pair02
pair02MassFromCollisionPairs = refl

pair03MassFromCollisionPairs :
  conditionalMass pair03 ≡ candidates pair03 + 2 * collisionPairs pair03
pair03MassFromCollisionPairs = refl

pair03EnumerationHasNoCollisionPair : collisionPairs pair03 ≡ 0
pair03EnumerationHasNoCollisionPair = refl

pair03EnumerationUsesAllImages : images pair03 ≡ candidates pair03
pair03EnumerationUsesAllImages = refl

pair03EnumerationHasUnitMaxFibre : maxFibre pair03 ≡ 1
pair03EnumerationHasUnitMaxFibre = refl

------------------------------------------------------------------------
-- Semantic raw-signature injectivity interface.
--
-- The numerical profile above is a pinned exhaustive-computation result.  A
-- semantic theorem that some raw signature determines a carrier element should
-- consume an explicit injectivity certificate rather than silently treating the
-- Python enumeration as a kernel proof.
------------------------------------------------------------------------

RawInjectiveOn : ∀ {Secret Raw : Set} → (Secret → Raw) → Set
RawInjectiveOn raw =
  ∀ left right → raw left ≡ raw right → left ≡ right

rawInjectiveCollapsesRawFibre :
  ∀ {Secret Raw : Set}
    (raw : Secret → Raw) →
  RawInjectiveOn raw →
  ∀ left right → raw left ≡ raw right → left ≡ right
rawInjectiveCollapsesRawFibre raw injective left right sameRaw =
  injective left right sameRaw

------------------------------------------------------------------------
-- Observation coarsening boundary.
--
-- A real implementation generally exposes observe(raw(secret)), not raw(secret)
-- itself.  Equal raw signatures always remain equal after coarsening, but the
-- converse need not hold.  The tiny counterexample below makes this logical
-- boundary kernel-visible.
------------------------------------------------------------------------

record ObservationCoarsening : Set₁ where
  constructor observation-coarsening
  field
    Secret Raw Observed : Set
    rawSignature : Secret → Raw
    observe : Raw → Observed

open ObservationCoarsening public

coarsenedObservation :
  (channel : ObservationCoarsening) →
  Secret channel → Observed channel
coarsenedObservation channel secret =
  observe channel (rawSignature channel secret)

sameRawImpliesSameObserved :
  ∀ (channel : ObservationCoarsening) left right →
  rawSignature channel left ≡ rawSignature channel right →
  coarsenedObservation channel left ≡ coarsenedObservation channel right
sameRawImpliesSameObserved channel left right refl = refl

data Secret2 : Set where
  secret0 secret1 : Secret2

data Raw2 : Set where
  raw0 raw1 : Raw2

data Observed1 : Set where
  observed : Observed1

raw2 : Secret2 → Raw2
raw2 secret0 = raw0
raw2 secret1 = raw1

observeConstant : Raw2 → Observed1
observeConstant raw0 = observed
observeConstant raw1 = observed

raw2Injective : RawInjectiveOn raw2
raw2Injective secret0 secret0 same = refl
raw2Injective secret0 secret1 ()
raw2Injective secret1 secret0 ()
raw2Injective secret1 secret1 same = refl

coarseningCounterexample : ObservationCoarsening
coarseningCounterexample =
  observation-coarsening Secret2 Raw2 Observed1 raw2 observeConstant

coarsenedPairCollides :
  coarsenedObservation coarseningCounterexample secret0 ≡
  coarsenedObservation coarseningCounterexample secret1
coarsenedPairCollides = refl

coarsenedPairSecretsDiffer : secret0 ≡ secret1 → ⊥
coarsenedPairSecretsDiffer ()

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
--
-- The three profile values are reproducible exhaustive finite-computation
-- regressions pinned in the Python script.  This Agda module checks their exact
-- arithmetic consequences and the semantic observation boundary; it does not
-- replay 390625-point enumeration in the kernel.
--
-- To promote the (0,3) raw collision-free result to a semantic Agda injectivity
-- theorem, provide a compact proof/certificate for the actual eight-coefficient
-- signature map.  To promote that further to an implementation leakage claim,
-- prove that the admitted physical observation channel preserves the required
-- distinctions.  Neither step is silently assumed here.
------------------------------------------------------------------------
