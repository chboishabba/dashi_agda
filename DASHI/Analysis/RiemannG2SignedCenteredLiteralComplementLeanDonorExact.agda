module DASHI.Analysis.RiemannG2SignedCenteredLiteralComplementLeanDonorExact where

------------------------------------------------------------------------
-- SIGNED CENTERED LITERAL-COMPLEMENT DONOR
--
-- Companion Lean source now distinguishes the actual literal Gamma cone from
-- the unswitched Gamma-response pair.
--
-- Let
--
--   S(g,t,r) = Off(g,t,r) + Q_Gamma(g,t,r),
--
-- on the final universal even-cone consumer.
--
-- Source-written:
--
--   |S(g,t,r) - S(g,t,0)| <= r^2 * E_center(g,Lambda,t),
--
-- hence
--
--   S(g,t,r) <= S(g,t,0) + r^2 * E_center(g,Lambda,t).
--
-- This is the consumer-faithful signed-centered donor.
--
-- However, radius zero is not automatically the pole-quotient baseline.  The
-- explicit taper kills the pole response at the selected positive radius, not
-- at radius zero.  For a short taper the source also proves
--
--   -S(g,t,0) = Cluster(g,t,0) + Pole(g,t,0).
--
-- Therefore complementChannels_pinned at the selected pole-killing radius does
-- NOT by itself produce S(0) <= baselineCluster.  A same-object/sign/pole
-- baseline theorem would still be needed before the conditional signed chain
--
--   S(r) <= S(0)+E,  S(0)<=B0,  E<M  ==>  S(r)<B0+M
--
-- can be used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record SignedCenteredLiteralComplementLeanReceipt : Set where
  constructor signed-centered-literal-complement-lean-receipt
  field
    repository : String
    branch : String
    literalCenteredPath : String
    signedReductionPath : String
    regressionPath : String
    literalCenteredCommit : String
    signedReductionCommit : String
    regressionCommit : String

open SignedCenteredLiteralComplementLeanReceipt public

currentSignedCenteredLiteralComplementLeanReceipt :
  SignedCenteredLiteralComplementLeanReceipt
currentSignedCenteredLiteralComplementLeanReceipt =
  signed-centered-literal-complement-lean-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannFinalLiteralComplementCenteredQuadratic.lean"
    "Synthesis/RiemannFinalLiteralComplementSignedReduction.lean"
    "Synthesis/RiemannFinalLiteralComplementSignedReductionRegression.lean"
    "df1fdffda804e7ed2fca877ce9b399916f8e7098"
    "bed55d73ca581b6e801b183520b66ba99c930576"
    "60aa722e1c525ac6b3b0da1fe16f679f22099ec2"

record SignedCenteredLiteralComplementBoundary : Set where
  constructor signed-centered-literal-complement-boundary
  field
    literalFinalComplementDifferenceQuadraticSourceWritten : Bool
    literalFinalComplementOneSidedUpperSourceWritten : Bool
    projectiveBalanceRequired : Bool

    separateAbsoluteChannelBudgetsIntrinsicToCenteredDonor : Bool
    absoluteBaselineRouteCanonical : Bool

    radiusZeroPoleChannelAutomaticallyKilled : Bool
    complementChannelsPinnedDirectlyProvesRadiusZeroBaseline : Bool
    radiusZeroLiteralBalanceIncludesPoleSourceWritten : Bool

    signedBaselineIdentificationStillRequiredForBranchA : Bool
    signedBaselineIdentificationMayUseFinalBalanceToManufacturePayment : Bool

    adaptiveFiniteNearEstimateIntrinsicToWholeResponseCenteredTheorem : Bool
    adaptiveNearMayRemainRepresentationTransportDebt : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgda : Bool
    r2ClosedHere : Bool
    rhDerivedHere : Bool

open SignedCenteredLiteralComplementBoundary public

canonicalSignedCenteredLiteralComplementBoundary :
  SignedCenteredLiteralComplementBoundary
canonicalSignedCenteredLiteralComplementBoundary =
  signed-centered-literal-complement-boundary
    true
    true
    false

    false
    false

    false
    false
    true

    true
    false

    false
    true

    false
    false
    false
    false
