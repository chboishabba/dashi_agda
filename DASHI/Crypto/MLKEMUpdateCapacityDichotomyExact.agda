module DASHI.Crypto.MLKEMUpdateCapacityDichotomyExact where

------------------------------------------------------------------------
-- ML-KEM: UPDATE-LOCALITY / STATE-TRANSCRIPT CAPACITY DICHOTOMY
--
-- Primary cryptographic source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Finite-field uncertainty source used by the upstream support theorem:
-- Martino Borello; Patrick Sole,
-- "The uncertainty principle over finite fields",
-- Discrete Mathematics 345 (2022), 112670.
-- DOI: 10.1016/j.disc.2021.112670.
--
-- This is the first direct composition of the two independent obstructions now
-- available in Round 17:
--
--   (1) harmonic/update locality
--         128 <= sourceSupport * (touches + singularBudget)
--
--   (2) sufficient-state/readout capacity
--         protectedCount <= stateAlphabet^stateCells
--                           * transcriptAlphabet^transcriptDepth.
--
-- A concrete recovery architecture that supplies both certificates is therefore
-- simultaneously constrained in update locality and distinguishability
-- capacity.  No generic runtime or hardness lower bound is claimed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_; _+_; _*_)

import DASHI.Crypto.MLKEMBoundedCellTranscriptCapacityExact as Capacity

record UpdateCapacityCertificate : Set where
  constructor update-capacity-certificate
  field
    sourceSupport : Nat
    touches : Nat
    singularBudget : Nat

    protectedCount : Nat
    stateAlphabet : Nat
    stateCells : Nat
    transcriptAlphabet : Nat
    transcriptDepth : Nat

    uncertaintyUpdateBound :
      128 ≤ sourceSupport * (touches + singularBudget)

    protectedCapacityBound :
      protectedCount ≤
        Capacity.combinedStateTranscriptCapacity
          stateAlphabet stateCells transcriptAlphabet transcriptDepth

open UpdateCapacityCertificate public

updateLocalityConstraint :
  (certificate : UpdateCapacityCertificate) →
  128 ≤ sourceSupport certificate *
        (touches certificate + singularBudget certificate)
updateLocalityConstraint = uncertaintyUpdateBound

stateTranscriptConstraint :
  (certificate : UpdateCapacityCertificate) →
  protectedCount certificate ≤
    Capacity.combinedStateTranscriptCapacity
      (stateAlphabet certificate)
      (stateCells certificate)
      (transcriptAlphabet certificate)
      (transcriptDepth certificate)
stateTranscriptConstraint = protectedCapacityBound

------------------------------------------------------------------------
-- Bounded primitive radius specialization.
------------------------------------------------------------------------

import Data.Nat.Properties as NatP

boundedRadiusUpdateConstraint :
  (certificate : UpdateCapacityCertificate) →
  (radius : Nat) →
  sourceSupport certificate ≤ radius →
  128 ≤ radius * (touches certificate + singularBudget certificate)
boundedRadiusUpdateConstraint certificate radius withinRadius =
  NatP.≤-trans
    (uncertaintyUpdateBound certificate)
    (NatP.*-monoˡ-≤
      (touches certificate + singularBudget certificate)
      withinRadius)

------------------------------------------------------------------------
-- Full-rank specialization.
--
-- The zero singular budget is supplied as an equality rather than silently
-- assumed from generic ML-KEM syntax.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)

fullRankUpdateConstraint :
  (certificate : UpdateCapacityCertificate) →
  singularBudget certificate ≡ 0 →
  128 ≤ sourceSupport certificate * touches certificate
fullRankUpdateConstraint certificate fullRank =
  subst
    (λ sigma →
      128 ≤ sourceSupport certificate * (touches certificate + sigma))
    fullRank
    (uncertaintyUpdateBound certificate)

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY / CURRENT STATUS
--
-- The generic two-resource composition is complete here.  Round 17 now also
-- supplies several downstream specialisations that were previously listed as
-- missing:
--
--   * `MLKEMExactResidualTouchLowerBoundExact` gives a concrete update resource
--     for explicitly materialised exact residual states;
--   * `MLKEMFIPS203ProtectedSecretCapacityExact` fixes the protected carrier to
--     the FIPS secret-support geometry;
--   * `MLKEMFIPS203UpdateCapacityResourceExact` composes that FIPS carrier with
--     the update inequality;
--   * `MLKEMFIPS203CBDPriorSuccessBoundExact` and
--     `MLKEMFIPS203AverageSuccessResourceExact` refine support-wide capacity to
--     an average-success numerator under the explicit CBD product-prior model.
--
-- The live producers are therefore narrower: prove the FIPS-specific Fourier
-- support/local regular-singular certificate for the actual public map, and
-- prove finite state/readout bounds plus exact recovery factorisation for one
-- concrete verifier architecture (including any admitted physical observation
-- coarsening).  The resulting theorem is a representation-resource tradeoff,
-- not a general polynomial/exponential hardness or wall-clock theorem.
------------------------------------------------------------------------
