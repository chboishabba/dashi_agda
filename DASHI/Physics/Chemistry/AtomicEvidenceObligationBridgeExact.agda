module DASHI.Physics.Chemistry.AtomicEvidenceObligationBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Core.EvidenceObligationAuthoritySeparationExact as Governed
import DASHI.Physics.Chemistry.AtomicPeriodicTableRecoveryBoundary as Atomic
import DASHI.Physics.Closure.DialecticalAtomFrontierReceipt as DialecticalAtom

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
  Governed.governedClaimState
    (Four.assess true false)
    Governed.obligationsOpen
    Governed.authorityDenied

atomicCandidateSupportDoesNotPromoteRecovery :
  Governed.promotionGate atomicCandidateSupportedOnly ≡ false
atomicCandidateSupportDoesNotPromoteRecovery = refl

periodicTableRecoveryConsumesWitness :
  ∀ {boundary : Atomic.AtomicPeriodicTableRecoveryBoundary} →
  Atomic.PeriodicTableRecoveryWitness boundary →
  Atomic.PeriodicTableRecoveryWitness boundary
periodicTableRecoveryConsumesWitness = Atomic.periodicTableRecoveryAvailable

dialecticalAtomPromotionStillImpossible :
  DialecticalAtom.DialecticalAtomFrontierPromotion →
  Data.Empty.⊥
dialecticalAtomPromotionStillImpossible =
  DialecticalAtom.dialecticalAtomFrontierPromotionImpossibleHere

record AtomicEvidenceObligationBoundary : Set where
  field
    positiveAtomicEvidenceEqualsRecoveryWitnessClaimed : Bool
    orbitalShellValenceWitnessesRemainIndependent : Bool
    dialecticalAtomEqualsPhysicalAtomClaimed : Bool
    dialecticalBookkeepingPromotesPhysicsClaimed : Bool
    genericEvidenceObligationSeparationReused : Bool

canonicalAtomicEvidenceObligationBoundary : AtomicEvidenceObligationBoundary
canonicalAtomicEvidenceObligationBoundary = record
  { positiveAtomicEvidenceEqualsRecoveryWitnessClaimed = false
  ; orbitalShellValenceWitnessesRemainIndependent = true
  ; dialecticalAtomEqualsPhysicalAtomClaimed = false
  ; dialecticalBookkeepingPromotesPhysicsClaimed = false
  ; genericEvidenceObligationSeparationReused = true
  }
