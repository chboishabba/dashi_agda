{-# OPTIONS --safe #-}
module DASHI.Unified.YMGoal1TOECompatibilityExact where

------------------------------------------------------------------------
-- YANG-MILLS GOAL-1 COMPATIBILITY ADAPTER FOR THE FOCUSED DASHI TOE GRAPH
--
-- O. Objective.
-- Reuse the current branch Goal-1 owners in the normalized TOE import graph.
--
-- R. Reuse.
-- R435 owns the canonical selected B source.
-- R436 owns the finite A source.
-- R437 owns the Clay-facing local-QFT C source.
-- R438 owns the literal CMP116 rate-source compatibility surface.
-- R439 owns the same-H nontriviality compiler boundary.
-- Existing closure modules own continuum, mass-gap, and Clay non-promotion.
--
-- C. Construction.
-- This module exports aliases only.
-- It proves no new Yang-Mills estimate.
--
-- S. Scope.
-- The later R559/R474 source-native route remains the preferred donor lineage.
-- This module is a compatibility adapter for this older branch.
--
-- L. Lane.
-- This file owns only the Goal-1 to TOE import edge.
-- It does not edit or import ESD implementation surfaces.
--
-- P. Postcondition.
-- TOE consumers can inspect the current Goal-1 frontier and exact non-promotion
-- facts through one normalized module.
--
-- G. Governance.
-- Original theorem owners retain attribution.
-- Conditional proof levels remain conditional.
-- A finite or conditional result does not promote continuum Yang-Mills.
--
-- F. Verification.
-- Read-back must preserve exact owner names and exact false promotion proofs.
-- Kernel certification requires an exact-head Agda or CI receipt.
--
-- Preconditions.
-- The R435--R439 owners exist on this branch.
-- The canonical current YM mass-gap and continuum boundaries exist.
--
-- Invariants.
-- No theorem changes proof level in this adapter.
-- No carrier identity is added.
-- No ESD surface is modified.
-- No meta-introspector theorem is copied or reattributed.
--
-- Postconditions.
-- The A, B, C, and same-H source levels are visible to the TOE graph.
-- Continuum transfer remains false.
-- Continuum mass-gap promotion remains false.
-- Clay promotion remains false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel)

import DASHI.Unified.InvariantSpine as Spine
import DASHI.Unified.Physics as UnifiedPhysics

import DASHI.Physics.YangMills.BalabanCMP116CanonicalSelectedBSourceRound435Exact as R435
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119CanonicalASourceRound436Exact as R436
import DASHI.Physics.YangMills.YangMillsClayGoal1CanonicalCSourceRound437Exact as R437
import DASHI.Physics.YangMills.BalabanCMP116CanonicalLiteralRateSourceRound438Exact as R438
import DASHI.Physics.YangMills.YangMillsClayGoal1SameHNontrivialityRound439Exact as R439

import DASHI.Physics.Closure.YangMillsMassGapBoundary as MassGap
import DASHI.Physics.Closure.YMBTToFourDimensionalContinuumRouteBoundary as Continuum
import DASHI.Physics.Closure.YMClayPromotionBoundary as Clay

------------------------------------------------------------------------
-- Exact current-branch source levels.
------------------------------------------------------------------------

goal1FiniteASourceLevel : ProofLevel
goal1FiniteASourceLevel =
  R436.literalRound436CanonicalASourceLevel

goal1CanonicalSelectedBSourceLevel : ProofLevel
goal1CanonicalSelectedBSourceLevel =
  R435.literalRound435CanonicalSelectedSourceLevel

goal1LiteralCMP116RateSourceLevel : ProofLevel
goal1LiteralCMP116RateSourceLevel =
  R438.literalRound438CanonicalCMP116RateTheoremLevel

goal1LocalQFTCSourceLevel : ProofLevel
goal1LocalQFTCSourceLevel =
  R437.literalRound437Goal1CSourceLevel

goal1SameHNontrivialitySemanticBridgeLevel : ProofLevel
goal1SameHNontrivialitySemanticBridgeLevel =
  R439.literalRound439SameSystemSemanticBridgeLevel

------------------------------------------------------------------------
-- Exact non-promotion theorem reuse.
------------------------------------------------------------------------

yangMillsFormalProjectionRemainsNonPromoting :
  ∀ kind →
  Spine.objectProjectionPromotion UnifiedPhysics.yangMillsObject kind ≡ false
yangMillsFormalProjectionRemainsNonPromoting =
  Spine.canonicalInvariantObjectsDoNotPromoteFormalProjections
    UnifiedPhysics.yangMillsObject

yangMillsMassGapBoundaryStillNotPromoted :
  MassGap.YangMillsMassGapBoundaryReceipt.massGapPromoted
    MassGap.canonicalYangMillsMassGapBoundaryReceipt
  ≡ false
yangMillsMassGapBoundaryStillNotPromoted =
  MassGap.YangMillsMassGapBoundaryReceipt.massGapPromotedIsFalse
    MassGap.canonicalYangMillsMassGapBoundaryReceipt

flat4DContinuumTransferStillOpen :
  Continuum.flat4DContinuumTransferProvedHere ≡ false
flat4DContinuumTransferStillOpen =
  Continuum.flat4DContinuumTransferProvedHereIsFalse

continuumMassGapStillNotPromoted :
  Continuum.continuumMassGapPromoted ≡ false
continuumMassGapStillNotPromoted =
  Continuum.continuumMassGapPromotedIsFalse

clayYangMillsStillNotPromoted :
  Clay.clayYangMillsPromoted ≡ false
clayYangMillsStillNotPromoted =
  Clay.ClayPromotionBoundary.noClayPromotion
    Clay.clayPromotionBoundary

------------------------------------------------------------------------
-- ZKP frame.
------------------------------------------------------------------------

record YMGoal1TOEZKPFrame : Set where
  field
    objective : String
    reuseRule : String
    constructionRule : String
    scopeRule : String
    laneRule : String
    postconditionRule : String
    governanceRule : String
    verificationRule : String

    ownersExist : Bool
    ownersExistIsTrue : ownersExist ≡ true

    noNewScientificTheorem : Bool
    noNewScientificTheoremIsTrue : noNewScientificTheorem ≡ true

    laterSourceNativeRoutePreferred : Bool
    laterSourceNativeRoutePreferredIsTrue :
      laterSourceNativeRoutePreferred ≡ true

    continuumPromotionBlocked : Bool
    continuumPromotionBlockedIsFalse :
      continuumPromotionBlocked ≡ false

    clayPromotionBlocked : Bool
    clayPromotionBlockedIsFalse :
      clayPromotionBlocked ≡ false

open YMGoal1TOEZKPFrame public

canonicalYMGoal1TOEZKPFrame : YMGoal1TOEZKPFrame
canonicalYMGoal1TOEZKPFrame = record
  { objective =
      "Reuse current Goal-1 theorem owners in the focused DASHI TOE graph."
  ; reuseRule =
      "Reuse canonical theorem owners before adding adapters."
  ; constructionRule =
      "Export aliases and exact non-promotion proofs only."
  ; scopeRule =
      "Treat R435-R439 as branch compatibility surfaces; prefer the later source-native R474/R559 lineage when available."
  ; laneRule =
      "Keep Yang-Mills theorem ownership in the Yang-Mills lane and keep ESD surfaces unchanged."
  ; postconditionRule =
      "Expose A/B/C/same-H frontier levels and exact continuum, mass-gap, and Clay non-promotion facts."
  ; governanceRule =
      "Preserve attribution, proof levels, carrier distinctions, and fail-closed promotion."
  ; verificationRule =
      "Require exact-head preflight and Agda receipts before any kernel-green claim."
  ; ownersExist = true
  ; ownersExistIsTrue = refl
  ; noNewScientificTheorem = true
  ; noNewScientificTheoremIsTrue = refl
  ; laterSourceNativeRoutePreferred = true
  ; laterSourceNativeRoutePreferredIsTrue = refl
  ; continuumPromotionBlocked = Continuum.flat4DContinuumTransferProvedHere
  ; continuumPromotionBlockedIsFalse = flat4DContinuumTransferStillOpen
  ; clayPromotionBlocked = Clay.clayYangMillsPromoted
  ; clayPromotionBlockedIsFalse = clayYangMillsStillNotPromoted
  }
