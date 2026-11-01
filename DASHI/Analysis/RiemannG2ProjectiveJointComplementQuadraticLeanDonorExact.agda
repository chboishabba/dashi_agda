module DASHI.Analysis.RiemannG2ProjectiveJointComplementQuadraticLeanDonorExact where

------------------------------------------------------------------------
-- JOINT PROJECTIVE OFF + GAMMA QUADRATIC DONOR
--
-- Vendored theorem bytes already prove, on the SAME projective taper,
--
--   |D_off^proj(r)|   <= r^2 * C_off(g,Lambda,t)
--   |D_Gamma^proj(r)| <= r^2 * C_Gamma(g,Lambda,t).
--
-- Companion Lean source now composes these into one theorem:
--
--   |D_off^proj(r) + D_Gamma^proj(r)|
--     <= r^2 * (C_off + C_Gamma).
--
-- This is mathematically relevant to the final baseline-excess problem because
-- it preserves cancellation until determinant level.  It is NOT silently
-- promoted to the final RH producer: the repository explicitly distinguishes
-- the rank-two/projective taper from the final universal pole-quotient taper.
-- An explicit same-object taper/carrier bridge is mandatory before reuse.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotleRankTwoPoleQuotientLaneSeparationExact as Separation

record ProjectiveJointQuadraticLeanReceipt : Set where
  constructor projective-joint-quadratic-lean-receipt
  field
    repository : String
    branch : String
    sourcePath : String
    regressionPath : String
    theoremName : String
    sourceCommit : String
    regressionCommit : String

open ProjectiveJointQuadraticLeanReceipt public

currentProjectiveJointQuadraticLeanReceipt :
  ProjectiveJointQuadraticLeanReceipt
currentProjectiveJointQuadraticLeanReceipt =
  projective-joint-quadratic-lean-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannProjectiveJointComplementQuadratic.lean"
    "Synthesis/RiemannProjectiveJointComplementQuadraticRegression.lean"
    "Synthesis.exists_jointProjectiveComplementQuadraticEnvelope"
    "00a393eac89cb073cb809e191812cdc8e7a56c4f"
    "9dbd85c1e75fb38e0373e2732224aaab3fbd2b2d"

record ProjectiveJointQuadraticBoundary : Set where
  constructor projective-joint-quadratic-boundary
  field
    offProjectiveQuadraticTheoremVendored : Bool
    gammaProjectiveQuadraticTheoremVendored : Bool
    jointProjectiveQuadraticCompositionSourceWritten : Bool

    projectiveTaperDefinitionallyFinalUniversalPoleQuotientTaper : Bool
    projectiveBalancedStrictConsumerAdmissible : Bool
    finalPoleQuotientLaneUsesDifferentAdmissibleComparisonObject : Bool

    taperEqualityAloneSufficesForFinalReuse : Bool
    explicitResponseAndBalanceTransportRequiredForFinalReuse : Bool

    jointDonorMayBeUsedAfterFullSameObjectBridge : Bool
    jointDonorAlreadyPaysFinalR2 : Bool
    leanTheoremTransportedIntoAgda : Bool
    rhDerivedHere : Bool

open ProjectiveJointQuadraticBoundary public

canonicalProjectiveJointQuadraticBoundary : ProjectiveJointQuadraticBoundary
canonicalProjectiveJointQuadraticBoundary =
  projective-joint-quadratic-boundary
    true
    true
    true
    false
    false
    true
    false
    true
    true
    false
    false
    false

projectiveCarrierFirewall :
  ProjectiveJointQuadraticBoundary.projectiveTaperDefinitionallyFinalUniversalPoleQuotientTaper
    canonicalProjectiveJointQuadraticBoundary ≡ false
projectiveCarrierFirewall = refl

projectiveBalancedStrictConsumerIsKnownNoGo :
  Separation.RankTwoPoleQuotientLaneSeparation.rankTwoStrictBalancedConsumerAdmissible
    Separation.canonicalRankTwoPoleQuotientLaneSeparation ≡ false
projectiveBalancedStrictConsumerIsKnownNoGo =
  Separation.rankTwoStrictBalancedConsumerAdmissibleIsFalse
    Separation.canonicalRankTwoPoleQuotientLaneSeparation

finalPoleQuotientLaneIsTheAdmissibleChangedComparison :
  Separation.RankTwoPoleQuotientLaneSeparation.poleQuotientFinalLaneAdmissible
    Separation.canonicalRankTwoPoleQuotientLaneSeparation ≡ true
finalPoleQuotientLaneIsTheAdmissibleChangedComparison =
  Separation.poleQuotientFinalLaneAdmissibleIsTrue
    Separation.canonicalRankTwoPoleQuotientLaneSeparation

taperOnlyBridgeIsInsufficient :
  ProjectiveJointQuadraticBoundary.taperEqualityAloneSufficesForFinalReuse
    canonicalProjectiveJointQuadraticBoundary ≡ false
taperOnlyBridgeIsInsufficient = refl

fullProjectiveReuseNeedsResponseAndBalanceTransport :
  ProjectiveJointQuadraticBoundary.explicitResponseAndBalanceTransportRequiredForFinalReuse
    canonicalProjectiveJointQuadraticBoundary ≡ true
fullProjectiveReuseNeedsResponseAndBalanceTransport = refl
