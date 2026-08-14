module DASHI.Crypto.MLKEMButterflyStageLocalityInvariantExact where

------------------------------------------------------------------------
-- ALL-STAGE FIPS-203 BUTTERFLY LOCALITY INVARIANT
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Round 17 found the endpoint identity
--
--   coefficient-local: 1 * (256*k),
--   scalar-NTT-local: 128 * (2*k),
--
-- both equal to 256*k.  Algorithm 9 exposes a stronger structural statement.
-- After j butterfly levels, one stage-local coordinate depends on 2^j source
-- coefficients, while one such stage coordinate fans through the remaining
-- levels to 2^(7-j) final same-parity scalar NTT coordinates.  BaseCaseMultiply
-- lets each final secret scalar affect two public scalar outputs in each of k
-- rows.  Therefore every canonical butterfly-stage locality choice has
--
--   priorWidth * publicFanout = 2^j * 2^(7-j) * 2*k = 256*k.
--
-- We prove this exactly for all eight canonical stages and all three approved
-- ML-KEM parameter sets.  This is a structural butterfly/dataflow invariant,
-- not a universal Fourier uncertainty theorem and not a work-factor bound.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; trans; sym)
open import Agda.Builtin.Nat using (Nat; _*_)

import DASHI.Crypto.MLKEMFIPS203SourceExact as FIPS

data ButterflyStage : Set where
  sourceStage
  stage1 stage2 stage3 stage4 stage5 stage6
  finalNTTStage : ButterflyStage

sourceSupportWidth : ButterflyStage → Nat
sourceSupportWidth sourceStage = 1
sourceSupportWidth stage1 = 2
sourceSupportWidth stage2 = 4
sourceSupportWidth stage3 = 8
sourceSupportWidth stage4 = 16
sourceSupportWidth stage5 = 32
sourceSupportWidth stage6 = 64
sourceSupportWidth finalNTTStage = 128

remainingScalarFanout : ButterflyStage → Nat
remainingScalarFanout sourceStage = 128
remainingScalarFanout stage1 = 64
remainingScalarFanout stage2 = 32
remainingScalarFanout stage3 = 16
remainingScalarFanout stage4 = 8
remainingScalarFanout stage5 = 4
remainingScalarFanout stage6 = 2
remainingScalarFanout finalNTTStage = 1

publicScalarFanout : FIPS.MLKEMParameters → ButterflyStage → Nat
publicScalarFanout p stage =
  remainingScalarFanout stage * (2 * FIPS.k p)

localityArea : FIPS.MLKEMParameters → ButterflyStage → Nat
localityArea p stage =
  sourceSupportWidth stage * publicScalarFanout p stage

------------------------------------------------------------------------
-- Exact approved-parameter invariants.
------------------------------------------------------------------------

mlKem512StageArea : ∀ stage → localityArea FIPS.params512 stage ≡ 512
mlKem512StageArea sourceStage = refl
mlKem512StageArea stage1 = refl
mlKem512StageArea stage2 = refl
mlKem512StageArea stage3 = refl
mlKem512StageArea stage4 = refl
mlKem512StageArea stage5 = refl
mlKem512StageArea stage6 = refl
mlKem512StageArea finalNTTStage = refl

mlKem768StageArea : ∀ stage → localityArea FIPS.params768 stage ≡ 768
mlKem768StageArea sourceStage = refl
mlKem768StageArea stage1 = refl
mlKem768StageArea stage2 = refl
mlKem768StageArea stage3 = refl
mlKem768StageArea stage4 = refl
mlKem768StageArea stage5 = refl
mlKem768StageArea stage6 = refl
mlKem768StageArea finalNTTStage = refl

mlKem1024StageArea : ∀ stage → localityArea FIPS.params1024 stage ≡ 1024
mlKem1024StageArea sourceStage = refl
mlKem1024StageArea stage1 = refl
mlKem1024StageArea stage2 = refl
mlKem1024StageArea stage3 = refl
mlKem1024StageArea stage4 = refl
mlKem1024StageArea stage5 = refl
mlKem1024StageArea stage6 = refl
mlKem1024StageArea finalNTTStage = refl

mlKem512AllStagesEqual :
  ∀ left right →
  localityArea FIPS.params512 left ≡ localityArea FIPS.params512 right
mlKem512AllStagesEqual left right =
  trans (mlKem512StageArea left) (sym (mlKem512StageArea right))

mlKem768AllStagesEqual :
  ∀ left right →
  localityArea FIPS.params768 left ≡ localityArea FIPS.params768 right
mlKem768AllStagesEqual left right =
  trans (mlKem768StageArea left) (sym (mlKem768StageArea right))

mlKem1024AllStagesEqual :
  ∀ left right →
  localityArea FIPS.params1024 left ≡ localityArea FIPS.params1024 right
mlKem1024AllStagesEqual left right =
  trans (mlKem1024StageArea left) (sym (mlKem1024StageArea right))

------------------------------------------------------------------------
-- Endpoint recovery: Round 17's coefficient/NTT equality is the first/last
-- case of the stronger all-stage theorem.
------------------------------------------------------------------------

mlKem512EndpointAreasEqual :
  localityArea FIPS.params512 sourceStage ≡
  localityArea FIPS.params512 finalNTTStage
mlKem512EndpointAreasEqual = mlKem512AllStagesEqual sourceStage finalNTTStage

record ButterflyLocalityBoundary : Set where
  constructor butterflyLocalityBoundary
  field
    allStageIdentityProvesAllRepresentationsObeySameArea : Set
    structuralAreaEqualsRuntimeWork : Set

open ButterflyLocalityBoundary public

canonicalButterflyLocalityBoundary : ButterflyLocalityBoundary
canonicalButterflyLocalityBoundary =
  butterflyLocalityBoundary
    (localityArea FIPS.params512 sourceStage ≡ 0)
    (localityArea FIPS.params512 finalNTTStage ≡ 0)
