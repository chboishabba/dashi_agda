module DASHI.Crypto.MLKEMFIPS203ProtectedSecretCapacityExact where

------------------------------------------------------------------------
-- ML-KEM / FIPS 203: PROTECTED SECRET-SUPPORT CAPACITY
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- This module instantiates the generic finite state x transcript capacity
-- theorem on a concrete ML-KEM protected object: the full coefficient-support
-- carrier of the K-PKE secret vector sampled by SamplePolyCBD_eta1.
--
-- For the three approved parameter sets the support carriers are exactly
--
--   ML-KEM-512  : 7^512
--   ML-KEM-768  : 5^768
--   ML-KEM-1024 : 5^1024.
--
-- These are support-carrier cardinalities, NOT entropy values, work factors,
-- or security-strength claims.  CBD probabilities are nonuniform.  The theorem
-- applies to exact recovery over the complete declared support carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)

import DASHI.Crypto.MLKEMFIPS203SourceExact as FIPS
import DASHI.Crypto.MLKEMFIPS203SearchGeometryExact as Search
import DASHI.Crypto.MLKEMBoundedCellTranscriptCapacityExact as Capacity

protectedSecretSupportCount : FIPS.MLKEMParameters → Nat
protectedSecretSupportCount = Search.naiveSecretSupportCarrier

protected512SupportCount :
  protectedSecretSupportCount FIPS.params512 ≡ Search.pow 7 512
protected512SupportCount = refl

protected768SupportCount :
  protectedSecretSupportCount FIPS.params768 ≡ Search.pow 5 768
protected768SupportCount = refl

protected1024SupportCount :
  protectedSecretSupportCount FIPS.params1024 ≡ Search.pow 5 1024
protected1024SupportCount = refl

------------------------------------------------------------------------
-- Source-specific capacity certificate.
--
-- The protected count is no longer a free Nat: it is fixed to the FIPS secret
-- support carrier for the selected parameter set.
------------------------------------------------------------------------

record FIPSProtectedSecretCapacity
    (parameters : FIPS.MLKEMParameters) : Set where
  constructor fips-protected-secret-capacity
  field
    stateAlphabet : Nat
    stateCells : Nat
    transcriptAlphabet : Nat
    transcriptDepth : Nat

    exactSecretRecoveryCapacity :
      protectedSecretSupportCount parameters ≤
      Capacity.combinedStateTranscriptCapacity
        stateAlphabet stateCells transcriptAlphabet transcriptDepth

open FIPSProtectedSecretCapacity public

fipsProtectedSecretCapacityBound :
  ∀ {parameters} →
  (certificate : FIPSProtectedSecretCapacity parameters) →
  protectedSecretSupportCount parameters ≤
  Capacity.combinedStateTranscriptCapacity
    (stateAlphabet certificate)
    (stateCells certificate)
    (transcriptAlphabet certificate)
    (transcriptDepth certificate)
fipsProtectedSecretCapacityBound = exactSecretRecoveryCapacity

mlKem512ProtectedCapacityBound :
  (certificate : FIPSProtectedSecretCapacity FIPS.params512) →
  Search.pow 7 512 ≤
  Capacity.combinedStateTranscriptCapacity
    (stateAlphabet certificate)
    (stateCells certificate)
    (transcriptAlphabet certificate)
    (transcriptDepth certificate)
mlKem512ProtectedCapacityBound = exactSecretRecoveryCapacity

mlKem768ProtectedCapacityBound :
  (certificate : FIPSProtectedSecretCapacity FIPS.params768) →
  Search.pow 5 768 ≤
  Capacity.combinedStateTranscriptCapacity
    (stateAlphabet certificate)
    (stateCells certificate)
    (transcriptAlphabet certificate)
    (transcriptDepth certificate)
mlKem768ProtectedCapacityBound = exactSecretRecoveryCapacity

mlKem1024ProtectedCapacityBound :
  (certificate : FIPSProtectedSecretCapacity FIPS.params1024) →
  Search.pow 5 1024 ≤
  Capacity.combinedStateTranscriptCapacity
    (stateAlphabet certificate)
    (stateCells certificate)
    (transcriptAlphabet certificate)
    (transcriptDepth certificate)
mlKem1024ProtectedCapacityBound = exactSecretRecoveryCapacity

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
--
-- The theorem fixes the protected carrier to the actual FIPS coefficient CBD
-- support geometry.  A concrete recovery architecture must still prove that:
--
--   * its maintained state has the claimed finite cell alphabet/count;
--   * its adaptive readout has the claimed branch alphabet/depth; and
--   * exact recovery of every support-secret factors through those resources.
--
-- Nothing here claims that an attacker must enumerate this support carrier.
------------------------------------------------------------------------
