module DASHI.Crypto.MLKEMFIPS203CBDPriorSuccessBoundExact where

------------------------------------------------------------------------
-- FIPS-203 CBD SECRET-PRIOR SUCCESS-MASS BOUND
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- SamplePolyCBD_eta maps 2*eta input bits to one coefficient equal to the
-- difference of two eta-bit Hamming weights.  Under the exact uniform-input-bit
-- CBD model, one coefficient therefore has raw-bit multiplicities
--
--   eta = 2 : 1,4,6,4,1       (total 16, maximum 6)
--   eta = 3 : 1,6,15,20,15,6,1 (total 64, maximum 20).
--
-- FIPS fixes eta1=3 for ML-KEM-512 and eta1=2 for ML-KEM-768/1024.  For N
-- independently supplied CBD coefficient bit-blocks, the maximum raw-bit
-- multiplicity of one complete secret vector is therefore
--
--   20^512, 6^768, 6^1024
--
-- out of total raw-bit weights
--
--   64^512, 16^768, 16^1024.
--
-- This module deliberately states the independence/uniform-bit condition as
-- the CBD product-prior model.  It does NOT identify that model with a theorem
-- that the deterministic SHAKE/PRF expansion in a concrete FIPS execution is a
-- truly independent random oracle output.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_; _*_; _^_)

import DASHI.Crypto.MLKEMFIPS203SourceExact as FIPS
import DASHI.Crypto.MLKEMFIPS203SearchGeometryExact as Geometry
import DASHI.Crypto.MLKEMBoundedCellTranscriptCapacityExact as Capacity
import DASHI.Crypto.MLKEMFinitePriorSuccessMassExact as Success

------------------------------------------------------------------------
-- Exact single-coefficient CBD raw-bit multiplicities needed by eta1.
------------------------------------------------------------------------

cbdRawOutcomeCount : Nat → Nat
cbdRawOutcomeCount eta = 2 ^ (2 * eta)

cbdMaxPointWeight : Nat → Nat
cbdMaxPointWeight zero = 1
cbdMaxPointWeight (suc zero) = 2
cbdMaxPointWeight (suc (suc zero)) = 6
cbdMaxPointWeight (suc (suc (suc zero))) = 20
cbdMaxPointWeight _ = 0

eta2RawOutcomes : cbdRawOutcomeCount 2 ≡ 16
eta2RawOutcomes = refl

eta3RawOutcomes : cbdRawOutcomeCount 3 ≡ 64
eta3RawOutcomes = refl

eta2MaxWeight : cbdMaxPointWeight 2 ≡ 6
eta2MaxWeight = refl

eta3MaxWeight : cbdMaxPointWeight 3 ≡ 20
eta3MaxWeight = refl

------------------------------------------------------------------------
-- Complete secret-vector product-prior weights.
------------------------------------------------------------------------

secretCBDTotalRawWeight : FIPS.MLKEMParameters → Nat
secretCBDTotalRawWeight p =
  cbdRawOutcomeCount (FIPS.eta1 p) ^ Geometry.secretCoefficientCount p

secretCBDMaxPointWeight : FIPS.MLKEMParameters → Nat
secretCBDMaxPointWeight p =
  cbdMaxPointWeight (FIPS.eta1 p) ^ Geometry.secretCoefficientCount p

mlKem512CBDTotalRawWeight :
  secretCBDTotalRawWeight FIPS.params512 ≡ 64 ^ 512
mlKem512CBDTotalRawWeight = refl

mlKem768CBDTotalRawWeight :
  secretCBDTotalRawWeight FIPS.params768 ≡ 16 ^ 768
mlKem768CBDTotalRawWeight = refl

mlKem1024CBDTotalRawWeight :
  secretCBDTotalRawWeight FIPS.params1024 ≡ 16 ^ 1024
mlKem1024CBDTotalRawWeight = refl

mlKem512CBDMaxPointWeight :
  secretCBDMaxPointWeight FIPS.params512 ≡ 20 ^ 512
mlKem512CBDMaxPointWeight = refl

mlKem768CBDMaxPointWeight :
  secretCBDMaxPointWeight FIPS.params768 ≡ 6 ^ 768
mlKem768CBDMaxPointWeight = refl

mlKem1024CBDMaxPointWeight :
  secretCBDMaxPointWeight FIPS.params1024 ≡ 6 ^ 1024
mlKem1024CBDMaxPointWeight = refl

------------------------------------------------------------------------
-- Average recovery-success mass through a bounded state/transcript carrier.
--
-- `successWeight` is the number of uniform CBD input-bit strings whose secret
-- labels fall in the architecture's successful recovery set.  Therefore the
-- corresponding success probability is exactly
--
--     successWeight / secretCBDTotalRawWeight p
--
-- in the product-CBD model.  We remain division-free in the kernel theorem.
------------------------------------------------------------------------

record FIPSCBDProductPriorRecovery : Set where
  constructor fips-cbd-product-prior-recovery
  field
    parameters : FIPS.MLKEMParameters

    stateAlphabet : Nat
    stateCells : Nat
    transcriptAlphabet : Nat
    transcriptDepth : Nat

    successCount : Nat
    successWeight : Nat

    successfulLabelsFitArchitecture :
      successCount ≤
        Capacity.combinedStateTranscriptCapacity
          stateAlphabet stateCells transcriptAlphabet transcriptDepth

    successfulCBDWeightWithinMaxPointMass :
      successWeight ≤
        successCount * secretCBDMaxPointWeight parameters

open FIPSCBDProductPriorRecovery public

fipsCBDRecoverySuccessWeightBound :
  (recovery : FIPSCBDProductPriorRecovery) →
  successWeight recovery ≤
    Capacity.combinedStateTranscriptCapacity
      (stateAlphabet recovery)
      (stateCells recovery)
      (transcriptAlphabet recovery)
      (transcriptDepth recovery)
    * secretCBDMaxPointWeight (parameters recovery)
fipsCBDRecoverySuccessWeightBound recovery =
  Success.successMassBound
    (successCount recovery)
    (Capacity.combinedStateTranscriptCapacity
      (stateAlphabet recovery)
      (stateCells recovery)
      (transcriptAlphabet recovery)
      (transcriptDepth recovery))
    (secretCBDMaxPointWeight (parameters recovery))
    (successWeight recovery)
    (successfulLabelsFitArchitecture recovery)
    (successfulCBDWeightWithinMaxPointMass recovery)

------------------------------------------------------------------------
-- Parameter-set-facing theorem surfaces.
------------------------------------------------------------------------

mlKem512SuccessNumeratorBound :
  (stateAlphabet stateCells transcriptAlphabet transcriptDepth
   successCount successWeight : Nat) →
  successCount ≤
    Capacity.combinedStateTranscriptCapacity
      stateAlphabet stateCells transcriptAlphabet transcriptDepth →
  successWeight ≤ successCount * (20 ^ 512) →
  successWeight ≤
    Capacity.combinedStateTranscriptCapacity
      stateAlphabet stateCells transcriptAlphabet transcriptDepth
    * (20 ^ 512)
mlKem512SuccessNumeratorBound
  stateAlphabet stateCells transcriptAlphabet transcriptDepth
  successCount successWeight countBound massBound =
  Success.successMassBound
    successCount
    (Capacity.combinedStateTranscriptCapacity
      stateAlphabet stateCells transcriptAlphabet transcriptDepth)
    (20 ^ 512)
    successWeight
    countBound massBound

mlKem768SuccessNumeratorBound :
  (stateAlphabet stateCells transcriptAlphabet transcriptDepth
   successCount successWeight : Nat) →
  successCount ≤
    Capacity.combinedStateTranscriptCapacity
      stateAlphabet stateCells transcriptAlphabet transcriptDepth →
  successWeight ≤ successCount * (6 ^ 768) →
  successWeight ≤
    Capacity.combinedStateTranscriptCapacity
      stateAlphabet stateCells transcriptAlphabet transcriptDepth
    * (6 ^ 768)
mlKem768SuccessNumeratorBound
  stateAlphabet stateCells transcriptAlphabet transcriptDepth
  successCount successWeight countBound massBound =
  Success.successMassBound
    successCount
    (Capacity.combinedStateTranscriptCapacity
      stateAlphabet stateCells transcriptAlphabet transcriptDepth)
    (6 ^ 768)
    successWeight
    countBound massBound

mlKem1024SuccessNumeratorBound :
  (stateAlphabet stateCells transcriptAlphabet transcriptDepth
   successCount successWeight : Nat) →
  successCount ≤
    Capacity.combinedStateTranscriptCapacity
      stateAlphabet stateCells transcriptAlphabet transcriptDepth →
  successWeight ≤ successCount * (6 ^ 1024) →
  successWeight ≤
    Capacity.combinedStateTranscriptCapacity
      stateAlphabet stateCells transcriptAlphabet transcriptDepth
    * (6 ^ 1024)
mlKem1024SuccessNumeratorBound
  stateAlphabet stateCells transcriptAlphabet transcriptDepth
  successCount successWeight countBound massBound =
  Success.successMassBound
    successCount
    (Capacity.combinedStateTranscriptCapacity
      stateAlphabet stateCells transcriptAlphabet transcriptDepth)
    (6 ^ 1024)
    successWeight
    countBound massBound

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
--
-- The exact denominator/maximum-point pairs are, under the uniform independent
-- CBD input-bit model:
--
--   ML-KEM-512  : max point 20^512 / 64^512
--   ML-KEM-768  : max point  6^768 / 16^768
--   ML-KEM-1024 : max point  6^1024 / 16^1024.
--
-- The theorem therefore converts finite code capacity into an average success
-- bound for that product prior.  It is not yet a theorem about the exact output
-- distribution of the deterministic SHAKE expansion from every FIPS KeyGen
-- seed, and it is not a runtime/hardness theorem.
------------------------------------------------------------------------
