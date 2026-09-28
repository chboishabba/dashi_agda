module DASHI.Analysis.RiemannSSP15DepthFiveRoleCodecExact where

------------------------------------------------------------------------
-- RH DEPTH-FIVE ROLE / SSP15 INTERNAL-LANE INDEXING CODEC
--
-- The RH primitive kernel has three provenance-labelled depth-five roles:
--
--   O, j, s
--
-- while SSP15 independently owns
--
--   ComplementMode5 × BalancedPhase3.
--
-- DASHI contribution here:
--
--   ComplementMode5 × RHDepthFiveRole
--      ≃
--   SSP15InternalLane
--
-- by an explicit three-role <-> balanced-phase indexing.
--
-- This is an EXACT FINITE INDEXING EQUIVALENCE ONLY.
--
-- It does NOT identify:
--   O with negative phase,
--   j with zero phase,
--   s with positive phase,
-- or the RH analytic provenance with the SSP15 phase semantics.
--
-- Its purpose is to make the 5×3=15 cross-pollination type-safe while
-- preserving the attribution / semantic firewall.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Quotient
import DASHI.Biology.SSP15ComplementPhaseProjectorExact as SSP15

------------------------------------------------------------------------
-- 1. Provenance-labelled RH depth-five roles.
------------------------------------------------------------------------

data RHDepthFiveRole : Set where
  originRole
  jRole
  sRole : RHDepthFiveRole

rhDepthFiveRoleCount : Nat
rhDepthFiveRoleCount = 3

rhDepthFiveRoleCountIsThree :
  rhDepthFiveRoleCount ≡ 3
rhDepthFiveRoleCountIsThree = refl

------------------------------------------------------------------------
-- 2. Explicit indexing between RH roles and balanced phases.
------------------------------------------------------------------------

roleToPhase :
  RHDepthFiveRole ->
  SSP15.BalancedPhase
roleToPhase originRole = Harmonic.negativeTrit
roleToPhase jRole = Harmonic.zeroTrit
roleToPhase sRole = Harmonic.positiveTrit

phaseToRole :
  SSP15.BalancedPhase ->
  RHDepthFiveRole
phaseToRole Harmonic.negativeTrit = originRole
phaseToRole Harmonic.zeroTrit = jRole
phaseToRole Harmonic.positiveTrit = sRole

roleAfterPhase :
  (phase : SSP15.BalancedPhase) ->
  roleToPhase (phaseToRole phase) ≡ phase
roleAfterPhase Harmonic.negativeTrit = refl
roleAfterPhase Harmonic.zeroTrit = refl
roleAfterPhase Harmonic.positiveTrit = refl

phaseAfterRole :
  (role : RHDepthFiveRole) ->
  phaseToRole (roleToPhase role) ≡ role
phaseAfterRole originRole = refl
phaseAfterRole jRole = refl
phaseAfterRole sRole = refl

------------------------------------------------------------------------
-- 3. Five modes × three RH roles.
------------------------------------------------------------------------

RHSSP15RoleCode : Set
RHSSP15RoleCode =
  Quotient.ComplementMode5 × RHDepthFiveRole

encodeRoleCode :
  RHSSP15RoleCode ->
  SSP15.SSP15InternalLane
encodeRoleCode (mode , role) =
  mode , roleToPhase role

decodeRoleCode :
  SSP15.SSP15InternalLane ->
  RHSSP15RoleCode
decodeRoleCode (mode , phase) =
  mode , phaseToRole phase

decodeAfterEncode :
  (code : RHSSP15RoleCode) ->
  decodeRoleCode (encodeRoleCode code) ≡ code
decodeAfterEncode (mode , role)
  rewrite phaseAfterRole role =
  refl

encodeAfterDecode :
  (lane : SSP15.SSP15InternalLane) ->
  encodeRoleCode (decodeRoleCode lane) ≡ lane
encodeAfterDecode (mode , phase)
  rewrite roleAfterPhase phase =
  refl

------------------------------------------------------------------------
-- 4. Cardinality / lane-count bridge.
------------------------------------------------------------------------

fiveModesTimesThreeRolesIsFifteen :
  5 * rhDepthFiveRoleCount ≡ 15
fiveModesTimesThreeRolesIsFifteen = refl

ssp15InternalLaneCountReused :
  SSP15.listCount SSP15.canonicalSSP15InternalLanes ≡ 15
ssp15InternalLaneCountReused =
  SSP15.ssp15InternalLaneCountIsFifteen

------------------------------------------------------------------------
-- 5. Phase-reversal transported as a role involution.
------------------------------------------------------------------------

reverseRHRole :
  RHDepthFiveRole ->
  RHDepthFiveRole
reverseRHRole originRole = sRole
reverseRHRole jRole = jRole
reverseRHRole sRole = originRole

reverseRHRoleInvolutive :
  (role : RHDepthFiveRole) ->
  reverseRHRole (reverseRHRole role) ≡ role
reverseRHRoleInvolutive originRole = refl
reverseRHRoleInvolutive jRole = refl
reverseRHRoleInvolutive sRole = refl

roleToPhaseIntertwinesReversal :
  (role : RHDepthFiveRole) ->
  roleToPhase (reverseRHRole role)
  ≡ SSP15.reverseBalancedPhase (roleToPhase role)
roleToPhaseIntertwinesReversal originRole = refl
roleToPhaseIntertwinesReversal jRole = refl
roleToPhaseIntertwinesReversal sRole = refl

------------------------------------------------------------------------
-- 6. Semantic / attribution firewall.
------------------------------------------------------------------------

data RHOriginRoleIsNegativeSSPPhase : Set where
data RHJRoleIsNeutralSSPPhase : Set where
data RHSRoleIsPositiveSSPPhase : Set where
data RHDepthFiveBlockIsSSP15InternalLaneSemantics : Set where
data FifteenCountCreatesCanonicalPrimeAssignment : Set where

originRoleNotPromotedToNegativeSSPPhaseSemantics :
  RHOriginRoleIsNegativeSSPPhase -> ⊥
originRoleNotPromotedToNegativeSSPPhaseSemantics ()

jRoleNotPromotedToNeutralSSPPhaseSemantics :
  RHJRoleIsNeutralSSPPhase -> ⊥
jRoleNotPromotedToNeutralSSPPhaseSemantics ()

sRoleNotPromotedToPositiveSSPPhaseSemantics :
  RHSRoleIsPositiveSSPPhase -> ⊥
sRoleNotPromotedToPositiveSSPPhaseSemantics ()

depthFiveBlockNotPromotedToSSP15Semantics :
  RHDepthFiveBlockIsSSP15InternalLaneSemantics -> ⊥
depthFiveBlockNotPromotedToSSP15Semantics ()

fifteenCountDoesNotCreatePrimeAssignment :
  FifteenCountCreatesCanonicalPrimeAssignment -> ⊥
fifteenCountDoesNotCreatePrimeAssignment ()

record RiemannSSP15DepthFiveRoleCodecBoundary : Set where
  constructor riemann-ssp15-depth-five-role-codec-boundary
  field
    rhDepthFiveRolesExplicit : Bool
    threeRolePhaseIndexingBijectionOwned : Bool
    fiveByThreeCodeToSSP15LaneBijectionOwned : Bool
    fifteenCountRecovered : Bool
    reversalIntertwiningOwned : Bool
    rolePhaseSemanticIdentityClaimed : Bool
    rhDepthFiveBlockPromotedToSSP15Semantics : Bool
    canonicalOggPrimeAssignmentCreatedHere : Bool

canonicalRiemannSSP15DepthFiveRoleCodecBoundary :
  RiemannSSP15DepthFiveRoleCodecBoundary
canonicalRiemannSSP15DepthFiveRoleCodecBoundary =
  riemann-ssp15-depth-five-role-codec-boundary
    true true true true true false false false
