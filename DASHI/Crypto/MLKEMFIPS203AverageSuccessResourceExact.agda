module DASHI.Crypto.MLKEMFIPS203AverageSuccessResourceExact where

------------------------------------------------------------------------
-- FIPS-203: UPDATE-LOCALITY / AVERAGE-SUCCESS RESOURCE TRADEOFF
--
-- This composes the two strongest currently source-facing Round-17 surfaces:
--
--   128 <= sourceSupport * (touches + singularBudget)
--
-- and, under the uniform-independent CBD input-bit product model,
--
--   successWeight <= stateTranscriptCapacity * maxSecretPointWeight.
--
-- The second inequality is an average-case success-numerator bound, not merely
-- a support-wide exact-recovery cardinality obstruction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (subst)
import Data.Nat.Properties as NatP

import DASHI.Crypto.MLKEMFIPS203SourceExact as FIPS
import DASHI.Crypto.MLKEMBoundedCellTranscriptCapacityExact as Capacity
import DASHI.Crypto.MLKEMFIPS203CBDPriorSuccessBoundExact as CBD

record FIPSAverageSuccessResourceCertificate : Set where
  constructor fips-average-success-resource-certificate
  field
    parameters : FIPS.MLKEMParameters

    sourceSupport : Nat
    touches : Nat
    singularBudget : Nat

    stateAlphabet : Nat
    stateCells : Nat
    transcriptAlphabet : Nat
    transcriptDepth : Nat

    successWeight : Nat

    uncertaintyUpdateBound :
      128 ≤ sourceSupport * (touches + singularBudget)

    cbdAverageSuccessNumeratorBound :
      successWeight ≤
        Capacity.combinedStateTranscriptCapacity
          stateAlphabet stateCells transcriptAlphabet transcriptDepth
        * CBD.secretCBDMaxPointWeight parameters

open FIPSAverageSuccessResourceCertificate public

updateResourceConstraint :
  (certificate : FIPSAverageSuccessResourceCertificate) →
  128 ≤ sourceSupport certificate *
        (touches certificate + singularBudget certificate)
updateResourceConstraint = uncertaintyUpdateBound

averageSuccessNumeratorConstraint :
  (certificate : FIPSAverageSuccessResourceCertificate) →
  successWeight certificate ≤
    Capacity.combinedStateTranscriptCapacity
      (stateAlphabet certificate)
      (stateCells certificate)
      (transcriptAlphabet certificate)
      (transcriptDepth certificate)
    * CBD.secretCBDMaxPointWeight (parameters certificate)
averageSuccessNumeratorConstraint = cbdAverageSuccessNumeratorBound

------------------------------------------------------------------------
-- Bounded source-move radius.
------------------------------------------------------------------------

boundedRadiusAverageSuccessResource :
  (certificate : FIPSAverageSuccessResourceCertificate) →
  (radius : Nat) →
  sourceSupport certificate ≤ radius →
  128 ≤ radius * (touches certificate + singularBudget certificate)
boundedRadiusAverageSuccessResource certificate radius withinRadius =
  NatP.≤-trans
    (uncertaintyUpdateBound certificate)
    (NatP.*-monoˡ-≤
      (touches certificate + singularBudget certificate)
      withinRadius)

------------------------------------------------------------------------
-- Full-rank update specialization.
------------------------------------------------------------------------

fullRankAverageSuccessUpdateConstraint :
  (certificate : FIPSAverageSuccessResourceCertificate) →
  singularBudget certificate ≡ 0 →
  128 ≤ sourceSupport certificate * touches certificate
fullRankAverageSuccessUpdateConstraint certificate fullRank =
  subst
    (λ sigma →
      128 ≤ sourceSupport certificate * (touches certificate + sigma))
    fullRank
    (uncertaintyUpdateBound certificate)

------------------------------------------------------------------------
-- Exact denominator surface for interpreting the success numerator.
--
-- In the CBD product-prior model the success probability represented by the
-- certificate is
--
--   successWeight / secretCBDTotalRawWeight parameters.
--
-- Keeping numerator and denominator separate avoids importing rational-order
-- machinery into this composition layer.
------------------------------------------------------------------------

successDenominator : FIPSAverageSuccessResourceCertificate → Nat
successDenominator certificate =
  CBD.secretCBDTotalRawWeight (parameters certificate)

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
--
-- A completed concrete ML-KEM theorem still needs to justify the harmonic
-- uncertainty/update premise for the actual public instance and identify the
-- considered state/transcript architecture.  The CBD probability statement is
-- exact for independent uniform SamplePolyCBD input-bit blocks; this file does
-- not promote SHAKE/PRF pseudorandomness into information-theoretic
-- independence.  No polynomial/exponential runtime lower bound is claimed.
------------------------------------------------------------------------
