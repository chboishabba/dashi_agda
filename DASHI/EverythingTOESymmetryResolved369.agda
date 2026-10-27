module DASHI.EverythingTOESymmetryResolved369 where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel)

------------------------------------------------------------------------
-- Focused TOE aggregate: generic symmetry-resolved fibre calculus plus the
-- existing SSP/369 representation-reduction and physics instances.
------------------------------------------------------------------------

import DASHI.Core.SymmetryResolvedFibreExact
import DASHI.EverythingSSPRepresentationReductionRound9
import DASHI.Physics.Closure.TOESymmetryResolved369BridgeExact

import DASHI.Unified.YMGoal1TOECompatibilityExact as YMGoal1TOE

------------------------------------------------------------------------
-- Current-branch Yang-Mills Goal-1 compatibility exports.
-- The theorem owners remain R435--R439 and the closure boundaries.
------------------------------------------------------------------------

toe369YangMillsGoal1FiniteASourceLevel : ProofLevel
toe369YangMillsGoal1FiniteASourceLevel =
  YMGoal1TOE.goal1FiniteASourceLevel

toe369YangMillsGoal1CanonicalSelectedBSourceLevel : ProofLevel
toe369YangMillsGoal1CanonicalSelectedBSourceLevel =
  YMGoal1TOE.goal1CanonicalSelectedBSourceLevel

toe369YangMillsGoal1LiteralCMP116RateSourceLevel : ProofLevel
toe369YangMillsGoal1LiteralCMP116RateSourceLevel =
  YMGoal1TOE.goal1LiteralCMP116RateSourceLevel

toe369YangMillsGoal1LocalQFTCSourceLevel : ProofLevel
toe369YangMillsGoal1LocalQFTCSourceLevel =
  YMGoal1TOE.goal1LocalQFTCSourceLevel

toe369YangMillsGoal1SameHNontrivialityLevel : ProofLevel
toe369YangMillsGoal1SameHNontrivialityLevel =
  YMGoal1TOE.goal1SameHNontrivialitySemanticBridgeLevel

toe369YangMillsFlat4DContinuumStillOpen :
  YMGoal1TOE.flat4DContinuumTransferProvedHere ≡ false
toe369YangMillsFlat4DContinuumStillOpen =
  YMGoal1TOE.flat4DContinuumTransferStillOpen

toe369YangMillsContinuumMassGapStillNotPromoted :
  YMGoal1TOE.continuumMassGapPromoted ≡ false
toe369YangMillsContinuumMassGapStillNotPromoted =
  YMGoal1TOE.continuumMassGapStillNotPromoted

toe369YangMillsClayStillNotPromoted :
  YMGoal1TOE.clayYangMillsPromoted ≡ false
toe369YangMillsClayStillNotPromoted =
  YMGoal1TOE.clayYangMillsStillNotPromoted

toe369YangMillsGoal1ZKPFrame : YMGoal1TOE.YMGoal1TOEZKPFrame
toe369YangMillsGoal1ZKPFrame =
  YMGoal1TOE.canonicalYMGoal1TOEZKPFrame
