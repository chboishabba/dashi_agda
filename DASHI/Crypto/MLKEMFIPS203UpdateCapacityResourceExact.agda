module DASHI.Crypto.MLKEMFIPS203UpdateCapacityResourceExact where

------------------------------------------------------------------------
-- ML-KEM / FIPS 203: SOURCE-SPECIFIC UPDATE x CAPACITY RESOURCE THEOREM
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- This module removes the last generic protected-count coordinate from the
-- update/capacity dichotomy.  Exact recovery over the full declared FIPS secret
-- support carrier must simultaneously satisfy
--
--   128 <= s * (t + sigma)
--
-- and
--
--   |SecretSupport_p| <= A^m * B^d.
--
-- Thus a concrete architecture is constrained both by local update geometry
-- and by sufficient state/readout capacity.  This remains a resource tradeoff,
-- not a generic runtime or hardness theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; _<_; _+_; _*_)
import Data.Nat.Properties as NatP

import DASHI.Crypto.MLKEMFIPS203SourceExact as FIPS
import DASHI.Crypto.MLKEMFIPS203ProtectedSecretCapacityExact as Protected
import DASHI.Crypto.MLKEMBoundedCellTranscriptCapacityExact as Capacity

record FIPSUpdateCapacityResource
    (parameters : FIPS.MLKEMParameters) : Set where
  constructor fips-update-capacity-resource
  field
    sourceSupport : Nat
    touches : Nat
    singularBudget : Nat

    stateAlphabet : Nat
    stateCells : Nat
    transcriptAlphabet : Nat
    transcriptDepth : Nat

    uncertaintyUpdateBound :
      128 ≤ sourceSupport * (touches + singularBudget)

    exactSecretRecoveryCapacity :
      Protected.protectedSecretSupportCount parameters ≤
      Capacity.combinedStateTranscriptCapacity
        stateAlphabet stateCells transcriptAlphabet transcriptDepth

open FIPSUpdateCapacityResource public

fipsUpdateLocalityConstraint :
  ∀ {parameters} →
  (resource : FIPSUpdateCapacityResource parameters) →
  128 ≤ sourceSupport resource *
        (touches resource + singularBudget resource)
fipsUpdateLocalityConstraint = uncertaintyUpdateBound

fipsSecretCapacityConstraint :
  ∀ {parameters} →
  (resource : FIPSUpdateCapacityResource parameters) →
  Protected.protectedSecretSupportCount parameters ≤
  Capacity.combinedStateTranscriptCapacity
    (stateAlphabet resource)
    (stateCells resource)
    (transcriptAlphabet resource)
    (transcriptDepth resource)
fipsSecretCapacityConstraint = exactSecretRecoveryCapacity

------------------------------------------------------------------------
-- Bounded source-move radius.
------------------------------------------------------------------------

boundedRadiusFIPSUpdateConstraint :
  ∀ {parameters} →
  (resource : FIPSUpdateCapacityResource parameters) →
  (radius : Nat) →
  sourceSupport resource ≤ radius →
  128 ≤ radius * (touches resource + singularBudget resource)
boundedRadiusFIPSUpdateConstraint resource radius withinRadius =
  NatP.≤-trans
    (uncertaintyUpdateBound resource)
    (NatP.*-monoˡ-≤
      (touches resource + singularBudget resource)
      withinRadius)

------------------------------------------------------------------------
-- Capacity falsifier.
--
-- If the proposed finite state x transcript carrier is strictly smaller than
-- the complete FIPS secret support carrier, exact support-wide recovery through
-- that resource is impossible.
------------------------------------------------------------------------

capacityDeficitRefutesFIPSResource :
  ∀ {parameters} →
  (resource : FIPSUpdateCapacityResource parameters) →
  Capacity.combinedStateTranscriptCapacity
    (stateAlphabet resource)
    (stateCells resource)
    (transcriptAlphabet resource)
    (transcriptDepth resource)
  < Protected.protectedSecretSupportCount parameters →
  ⊥
capacityDeficitRefutesFIPSResource resource deficit =
  NatP.<⇒≱ deficit (exactSecretRecoveryCapacity resource)

------------------------------------------------------------------------
-- Full-rank specialization supplied explicitly as sigma = 0.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)

fullRankFIPSUpdateConstraint :
  ∀ {parameters} →
  (resource : FIPSUpdateCapacityResource parameters) →
  singularBudget resource ≡ 0 →
  128 ≤ sourceSupport resource * touches resource
fullRankFIPSUpdateConstraint resource fullRank =
  subst
    (λ sigma →
      128 ≤ sourceSupport resource * (touches resource + sigma))
    fullRank
    (uncertaintyUpdateBound resource)

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
--
-- This theorem now fixes the protected object to the FIPS secret support
-- carrier, but still consumes the 128 uncertainty/update inequality as a
-- premise.  Closing that premise source-faithfully requires the exact FIPS
-- Fourier uncertainty + local regular/singular producer already isolated in
-- Round 17.  The finite-capacity side likewise applies to exact support-wide
-- recovery, not average-case success or security-strength entropy.
------------------------------------------------------------------------
