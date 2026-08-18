module DASHI.Physics.Chemistry.AtomicEvidenceObligationBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Core.EvidenceObligationAuthoritySeparationExact as Governed
import DASHI.Physics.Chemistry.AtomicPeriodicTableRecoveryBoundary as Atomic
import DASHI.Physics.Closure.DialecticalAtomFrontierReceipt as DialecticalAtom
import DASHI.Promotion.AuthorityGateCore as Authority

------------------------------------------------------------------------
-- Atomic evidence / recovery boundary.
--
-- A positive observation about one atomic coordinate does not discharge the
-- independent witnesses required for orbital spectrum, shell structure and
-- periodic valence recovery.  The dialectical "atom" lane is separately kept
-- as bookkeeping and is not promoted into the physical atom recovery theorem.
------------------------------------------------------------------------

atomicCandidateSupportedOnly : Governed.GovernedClaimState
atomicCandidateSupportedOnly =
  Governed.closedGovernedClaimState
    (Four.assess true false)
    Governed.obligationsOpen
    Authority.theoremAuthority
    "atomic candidate to periodic-table recovery theorem"

atomicCandidateSupportDoesNotPromoteRecovery :
  Governed.localPromotion atomicCandidateSupportedOnly ≡ false
atomicCandidateSupportDoesNotPromoteRecovery =
  Governed.localPromotionIsFalse atomicCandidateSupportedOnly

periodicTableRecoveryConsumesWitness :
  ∀ {boundary : Atomic.AtomicPeriodicTableRecoveryBoundary} →
  Atomic.PeriodicTableRecoveryWitness boundary →
  Atomic.PeriodicTableRecoveryWitness boundary
periodicTableRecoveryConsumesWitness = Atomic.periodicTableRecoveryAvailable

dialecticalAtomPromotionStillImpossible :
  DialecticalAtom.DialecticalAtomFrontierPromotion →
  ⊥
dialecticalAtomPromotionStillImpossible =
  DialecticalAtom.dialecticalAtomFrontierPromotionImpossibleHere

record AtomicEvidenceObligationBoundary : Set where
  field
    positiveAtomicEvidenceEqualsRecoveryWitnessClaimed : Bool
    orbitalShellValenceWitnessesRemainIndependent : Bool
    dialecticalAtomEqualsPhysicalAtomClaimed : Bool
    dialecticalBookkeepingPromotesPhysicsClaimed : Bool
    canonicalAuthorityGateCoreReused : Bool

canonicalAtomicEvidenceObligationBoundary : AtomicEvidenceObligationBoundary
canonicalAtomicEvidenceObligationBoundary = record
  { positiveAtomicEvidenceEqualsRecoveryWitnessClaimed = false
  ; orbitalShellValenceWitnessesRemainIndependent = true
  ; dialecticalAtomEqualsPhysicalAtomClaimed = false
  ; dialecticalBookkeepingPromotesPhysicsClaimed = false
  ; canonicalAuthorityGateCoreReused = true
  }
