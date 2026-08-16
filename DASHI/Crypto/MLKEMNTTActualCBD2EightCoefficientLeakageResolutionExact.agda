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
-- Pierre-Alain Fouque, Damien Marion, Quyen Nguyen, Alexandre Wallet,
-- "Avengers assemble! Supervised learning meets lattice reduction: A single
-- power trace attack against CRYSTALS-Kyber Key Generation",
-- IACR Transactions on Cryptographic Hardware and Embedded Systems 2025(4),
-- 409--436. DOI: 10.46586/tches.v2025.i4.409-436.
--
-- Guilhem Assael, Philippe Elbaz-Vincent, Guillaume Reymond,
-- "Improving Single-Trace Attacks on the Number-Theoretic Transform for
-- Cortex-M4", IEEE HOST 2023.
-- DOI: 10.1109/HOST55118.2023.10133270.
--
-- Tianrun Yu, Chi Cheng, Zilong Yang, Yingchen Wang, Yanbin Pan, Jian Weng,
-- "Hints from Hertz: Dynamic Frequency Scaling Side-Channel Analysis of
-- Number Theoretic Transform in Lattice-Based KEMs",
-- IACR Transactions on Cryptographic Hardware and Embedded Systems 2024(3),
-- 200--223. DOI: 10.46586/tches.v2024.i3.200-223.
--
-- These papers motivate defensive observation/coarsening audits only. Their
-- attack procedures are not imported as theorem premises.
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
-- Observation coarsening.
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

------------------------------------------------------------------------
-- Exact criterion for when a coarsening preserves the dangerous raw resolution.
--
-- This is the implementation-facing target for Hamming-weight/distance, timing,
-- masked-share, frequency, cache-line or other concrete channels: equality of
-- the *observed* values must reflect equality of the raw signatures on the
-- actual secret image.  Global injectivity of `observe` outside that image is
-- unnecessary.
------------------------------------------------------------------------

ObservationReflectsRawOnSecretImage : ObservationCoarsening → Set
ObservationReflectsRawOnSecretImage channel =
  ∀ left right →
  coarsenedObservation channel left ≡ coarsenedObservation channel right →
  rawSignature channel left ≡ rawSignature channel right

coarseningPreservesInjectivityExactlyWhenItReflectsRaw :
  (channel : ObservationCoarsening) →
  RawInjectiveOn (rawSignature channel) →
  ObservationReflectsRawOnSecretImage channel →
  RawInjectiveOn (coarsenedObservation channel)
coarseningPreservesInjectivityExactlyWhenItReflectsRaw
  channel rawInjective reflectsRaw left right observedSame =
  rawInjective left right (reflectsRaw left right observedSame)

record CoarseningCollisionWitness (channel : ObservationCoarsening) : Set where
  constructor coarsening-collision-witness
  field
    left right : Secret channel
    rawDifferent :
      rawSignature channel left ≡ rawSignature channel right → ⊥
    observedSame :
      coarsenedObservation channel left ≡ coarsenedObservation channel right

open CoarseningCollisionWitness public

coarseningCollisionRefutesObservedInjectivity :
  ∀ {channel : ObservationCoarsening} →
  CoarseningCollisionWitness channel →
  RawInjectiveOn (coarsenedObservation channel) →
  ⊥
coarseningCollisionRefutesObservedInjectivity witness observedInjective =
  rawDifferent witness
    (λ-equality-forbidden
      (observedInjective
        (left witness)
        (right witness)
        (observedSame witness)))
  where
  -- If the coarsened observation were injective, the two secrets would be
  -- equal; congruence of the raw signature would then contradict rawDifferent.
  λ-equality-forbidden :
    left witness ≡ right witness →
    rawSignature channel (left witness) ≡ rawSignature channel (right witness)
  λ-equality-forbidden refl = refl

------------------------------------------------------------------------
-- Tiny exact counterexample showing why raw injectivity cannot be promoted to
-- physical observation injectivity without the reflection criterion.
------------------------------------------------------------------------

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

rawPairDifferent : raw2 secret0 ≡ raw2 secret1 → ⊥
rawPairDifferent ()

finiteCoarseningCollision : CoarseningCollisionWitness coarseningCounterexample
finiteCoarseningCollision =
  coarsening-collision-witness secret0 secret1 rawPairDifferent refl

finiteCoarseningNotInjective :
  RawInjectiveOn (coarsenedObservation coarseningCounterexample) → ⊥
finiteCoarseningNotInjective =
  coarseningCollisionRefutesObservedInjectivity finiteCoarseningCollision

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY / CURRENT STATUS
--
-- The large 5^8 profile remains a reproducible discovery regression rather than
-- a kernel enumeration.  Round 17 now also contains the compact proof route:
--
--   MLKEMNTTPair03CubicRootFactorReductionExact
--     -> MLKEMNTTPair03ReducedKernelCertificateExact
--
-- which reduces the semantic raw-kernel problem to 81^2 = 6561 bounded states.
-- The remaining same-object step is the canonical F_3329 bridge from equality
-- of actual raw pair-(0,3) signatures to those reduced equations.
--
-- Separately, the theorem above identifies exactly what a real physical channel
-- must prove before raw injectivity matters: observation equality must reflect
-- raw-signature equality on the actual secret image.  No such implementation-
-- specific Hamming/timing/masking/frequency theorem is silently assumed.
------------------------------------------------------------------------
