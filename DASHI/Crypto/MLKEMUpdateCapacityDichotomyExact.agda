module DASHI.Crypto.MLKEMUpdateCapacityDichotomyExact where

------------------------------------------------------------------------
-- ML-KEM: UPDATE-LOCALITY / STATE-TRANSCRIPT CAPACITY DICHOTOMY
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
-- AUTHORITY BOUNDARY / COMPLETION TARGET
--
-- The final source-faithful ML-KEM theorem now needs concrete producers for:
--
--   * the finite-field uncertainty/update certificate;
--   * the maintained-state cell alphabet/count;
--   * the adaptive transcript alphabet/depth;
--   * exact protected-label recovery through that state/transcript pair.
--
-- Once instantiated, the resulting theorem is a representation-resource
-- tradeoff.  It still does not identify this tradeoff with a general
-- polynomial/exponential hardness theorem.
------------------------------------------------------------------------
