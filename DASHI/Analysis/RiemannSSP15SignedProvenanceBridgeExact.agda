module DASHI.Analysis.RiemannSSP15SignedProvenanceBridgeExact where

------------------------------------------------------------------------
-- RH DEPTH-FIVE ROLE -> SSP15 POINTED SIGNED PROVENANCE
--
-- Compose the guarded finite indexing codec
--
--   ComplementMode5 × {O,j,s}
--       <-> SSP15InternalLane
--
-- with the existing chosen SSP15/Ogg-prime indexing and pointed signed
-- FRACTRAN bridge.
--
-- This yields:
--
--   RH role code
--      -> existing SSP15 internal lane
--      -> chosen Ogg prime + signed unit multiplicity
--      -> full SSP valuation.
--
-- The POINTED layer reopens the finite role code exactly.
--
-- Crucially, jRole maps to zero signed multiplicity.  Therefore the full
-- valuation forgets which of the five neutral mode/prime choices produced it;
-- the selected prime / marked role provenance must remain above the coarse
-- valuation.
--
-- All prime assignments here are relative to the repository's explicitly
-- chosen OggInternalLaneBijection.  They are NOT promoted to externally
-- canonical arithmetic assignments.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

import DASHI.Analysis.RiemannSSP15DepthFiveRoleCodecExact as Codec
import DASHI.Biology.SSP15PrimeValuedStateExact as PrimeValued
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Quotient
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Moonshine.JInvariant369SSP15SignedFRACTRANBranchExact as Branch
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- 1. Role code -> chosen Ogg prime / pointed signed state.
------------------------------------------------------------------------

roleCodeToPrime :
  Codec.RHSSP15RoleCode ->
  Lane.MonsterPrimeLane
roleCodeToPrime code =
  Branch.internalToPrime (Codec.encodeRoleCode code)

roleCodeToPointedSigned :
  Codec.RHSSP15RoleCode ->
  Branch.PointedSignedSSPLane
roleCodeToPointedSigned code =
  Branch.internalLaneToPointedSigned (Codec.encodeRoleCode code)

pointedSelectedPrimeIsRoleCodePrime :
  (code : Codec.RHSSP15RoleCode) ->
  Branch.selectedPrime (roleCodeToPointedSigned code)
  ≡ roleCodeToPrime code
pointedSelectedPrimeIsRoleCodePrime code = refl

------------------------------------------------------------------------
-- 2. Exact reopening through the pointed layer.
------------------------------------------------------------------------

pointedSignedToRoleCode :
  Branch.PointedSignedSSPLane ->
  Codec.RHSSP15RoleCode
pointedSignedToRoleCode state =
  Codec.decodeRoleCode
    (Branch.pointedSignedToCoarseInternal state)

roleCodePointedRoundTrip :
  (code : Codec.RHSSP15RoleCode) ->
  pointedSignedToRoleCode (roleCodeToPointedSigned code) ≡ code
roleCodePointedRoundTrip code =
  trans
    (cong Codec.decodeRoleCode
      (Branch.internalPointedCoarseRoundTrip
        (Codec.encodeRoleCode code)))
    (Codec.decodeAfterEncode code)

------------------------------------------------------------------------
-- 3. The three RH roles become the existing UNIT signed multiplicities under
-- the chosen indexing.  This is an indexing law, not semantic identity.
------------------------------------------------------------------------

roleToUnitMultiplicity :
  Codec.RHDepthFiveRole ->
  Signed.SignedMultiplicity
roleToUnitMultiplicity role =
  Branch.phaseToUnitMultiplicity (Codec.roleToPhase role)

originRoleIndexesNegativeUnit :
  roleToUnitMultiplicity Codec.originRole
  ≡ Signed.negativeMultiplicity 1
originRoleIndexesNegativeUnit = refl

jRoleIndexesZero :
  roleToUnitMultiplicity Codec.jRole
  ≡ Signed.zeroMultiplicity
jRoleIndexesZero = refl

sRoleIndexesPositiveUnit :
  roleToUnitMultiplicity Codec.sRole
  ≡ Signed.positiveMultiplicity 1
sRoleIndexesPositiveUnit = refl

roleCodeSignedMultiplicityExact :
  (code : Codec.RHSSP15RoleCode) ->
  Branch.signedMultiplicity (roleCodeToPointedSigned code)
  ≡ roleToUnitMultiplicity (proj₂ code)
roleCodeSignedMultiplicityExact (mode , Codec.originRole) = refl
roleCodeSignedMultiplicityExact (mode , Codec.jRole) = refl
roleCodeSignedMultiplicityExact (mode , Codec.sRole) = refl

------------------------------------------------------------------------
-- 4. Role code -> full SSP valuation.
------------------------------------------------------------------------

roleCodeValuation :
  Codec.RHSSP15RoleCode ->
  Signed.SSPValuation
roleCodeValuation code =
  Branch.pointedSignedValuation (roleCodeToPointedSigned code)

roleCodeValuationOwnLane :
  (code : Codec.RHSSP15RoleCode) ->
  roleCodeValuation code
    (Branch.lanePrimeToSignedPrime (roleCodeToPrime code))
  ≡ roleToUnitMultiplicity (proj₂ code)
roleCodeValuationOwnLane code =
  trans
    (Branch.pointedValuationOwnLane
      (roleCodeToPointedSigned code))
    (roleCodeSignedMultiplicityExact code)

------------------------------------------------------------------------
-- 5. jRole demonstrates why the pointed provenance is necessary.
--
-- Every jRole code carries zero multiplicity, so its full valuation is the
-- zero valuation at every observed SSP prime.  The selected prime/mode cannot
-- be recovered from that coarse valuation alone.
------------------------------------------------------------------------

jRoleCode :
  Quotient.ComplementMode5 ->
  Codec.RHSSP15RoleCode
jRoleCode mode =
  mode , Codec.jRole

jRolePointedIsNeutral :
  (mode : Quotient.ComplementMode5) ->
  Branch.signedMultiplicity
    (roleCodeToPointedSigned (jRoleCode mode))
  ≡ Signed.zeroMultiplicity
jRolePointedIsNeutral mode = refl

jRoleValuationZeroAt :
  (mode : Quotient.ComplementMode5) ->
  (observed : Signed.SSPPrime) ->
  roleCodeValuation (jRoleCode mode) observed
  ≡ Signed.zeroMultiplicity
jRoleValuationZeroAt mode observed =
  Branch.neutralValuationIsZeroAt
    (roleCodeToPrime (jRoleCode mode))
    observed

data ZeroValuationRecoversRHMode : Set where

zeroValuationDoesNotRecoverRHMode :
  ZeroValuationRecoversRHMode -> ⊥
zeroValuationDoesNotRecoverRHMode ()

------------------------------------------------------------------------
-- 6. Lift into the existing prime-valued SSP15 state, preserving residual
-- geometry as an independent coordinate.
------------------------------------------------------------------------

RolePrimeValuedState : Set₁
RolePrimeValuedState =
  Σ Lane.MonsterPrimeLane PrimeValued.PrimeValuedSSP15State

attachRolePrimeValued :
  Codec.RHSSP15RoleCode ->
  PrimeValued.ResidualGeometryKind ->
  RolePrimeValuedState
attachRolePrimeValued code residual =
  roleCodeToPrime code
  ,
  PrimeValued.attachInternalLane
    (roleCodeToPrime code)
    (Codec.encodeRoleCode code)
    residual

attachedRoleInternalLaneExact :
  (code : Codec.RHSSP15RoleCode) ->
  (residual : PrimeValued.ResidualGeometryKind) ->
  PrimeValued.internalLane
    (proj₂ (attachRolePrimeValued code residual))
  ≡ Codec.encodeRoleCode code
attachedRoleInternalLaneExact code residual =
  PrimeValued.primeValuationDoesNotRestrictInternalLane
    (roleCodeToPrime code)
    (Codec.encodeRoleCode code)
    residual

attachedRoleReopensCode :
  (code : Codec.RHSSP15RoleCode) ->
  (residual : PrimeValued.ResidualGeometryKind) ->
  Codec.decodeRoleCode
    (PrimeValued.internalLane
      (proj₂ (attachRolePrimeValued code residual)))
  ≡ code
attachedRoleReopensCode code residual =
  trans
    (cong Codec.decodeRoleCode
      (attachedRoleInternalLaneExact code residual))
    (Codec.decodeAfterEncode code)

------------------------------------------------------------------------
-- 7. Attribution / semantic firewalls.
------------------------------------------------------------------------

data ChosenRolePrimeIsExternallyCanonical : Set where
data RHRoleIsSignedMultiplicitySemantics : Set where
data ZeroValuationErasesNoProvenance : Set where
data RHDepthFiveFlagIsMonsterPrimeValuation : Set where

chosenRolePrimeNotPromotedToExternalCanonicality :
  ChosenRolePrimeIsExternallyCanonical -> ⊥
chosenRolePrimeNotPromotedToExternalCanonicality ()

rhRoleNotPromotedToSignedMultiplicitySemantics :
  RHRoleIsSignedMultiplicitySemantics -> ⊥
rhRoleNotPromotedToSignedMultiplicitySemantics ()

zeroValuationDoesErasePointedProvenance :
  ZeroValuationErasesNoProvenance -> ⊥
zeroValuationDoesErasePointedProvenance ()

rhDepthFiveFlagNotPromotedToMonsterPrimeValuation :
  RHDepthFiveFlagIsMonsterPrimeValuation -> ⊥
rhDepthFiveFlagNotPromotedToMonsterPrimeValuation ()

record RiemannSSP15SignedProvenanceBoundary : Set where
  constructor riemann-ssp15-signed-provenance-boundary
  field
    roleCodeToChosenOggPrimeOwned : Bool
    roleCodeToPointedSignedOwned : Bool
    pointedRoleCodeRoundTripOwned : Bool
    roleToUnitMultiplicityIndexingOwned : Bool
    fullValuationCompilationOwned : Bool
    jRoleZeroValuationProvenanceLossOwned : Bool
    primeValuedResidualGeometryLiftOwned : Bool
    chosenPrimeAssignmentPromotedToExternalCanonicality : Bool
    rhRolePromotedToSignedMultiplicitySemantics : Bool
    rhDepthFiveFlagPromotedToMonsterValuation : Bool

canonicalRiemannSSP15SignedProvenanceBoundary :
  RiemannSSP15SignedProvenanceBoundary
canonicalRiemannSSP15SignedProvenanceBoundary =
  riemann-ssp15-signed-provenance-boundary
    true true true true true true true
    false false false
