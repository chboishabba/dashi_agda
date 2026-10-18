module DASHI.Analysis.RiemannG2CenteredOffExplicitHighLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- EXPLICIT CENTERED-OFF HIGH-ORDINATE DONOR
--
-- Companion Lean source now owns:
--
-- 1. an explicit centered reflection-pair curvature coefficient built from
--    Lambda, r and L1 masses of g,g',g'';
--
-- 2. an exact far-only centered Off upper inside J Lambda <= pi/2;
--
-- 3. the natural cutoff J=floor(|t|/9), valid for |t|>=18 and canonical support
--    Lambda <= 9*pi/(4|t|), with
--
--       1 <= J,
--       J Lambda <= pi/2,
--       |t|/18 <= J;
--
-- 4. the explicit far-shell estimate
--
--       farShellBound A |t| J
--         <= 324 A log(|t|+4)/|t|
--            + 72 A sqrt(18/|t|).
--
-- Thus the final centered Off response has a fully explicit high-ordinate
-- magnitude upper with no finite-near debt and no existential curvature
-- constant.
--
-- This is NOT claimed to decay for the canonical taper until the shrinking-bump
-- derivative masses are quantitatively controlled.  It is an auxiliary
-- magnitude theorem, not the uniform prize-facing sign theorem.
------------------------------------------------------------------------

record CenteredOffExplicitHighLeanReceipt : Set where
  constructor centered-off-explicit-high-lean-receipt
  field
    repository : String
    branch : String
    curvaturePath : String
    explicitFarOnlyPath : String
    cutoffPath : String
    highUpperPath : String
    curvatureCommit : String
    explicitFarOnlyCommit : String
    cutoffCommit : String
    highUpperCommit : String

open CenteredOffExplicitHighLeanReceipt public

currentCenteredOffExplicitHighLeanReceipt : CenteredOffExplicitHighLeanReceipt
currentCenteredOffExplicitHighLeanReceipt =
  centered-off-explicit-high-lean-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannCenteredPairCurvature.lean"
    "Synthesis/RiemannCenteredOffExplicitFarOnly.lean"
    "Synthesis/RiemannCanonicalSignedWindowCutoff.lean"
    "Synthesis/RiemannCenteredOffCanonicalHighUpper.lean"
    "5998c77dc00bbc5b4b51b91cececc6b1fe0d461a"
    "7ad8f2d202bc21069e8478bb89baf9a3b574c4b5"
    "dbb40d99d1dc6909954ef43106b3a22b2aafb0c6"
    "c45b1876c36668089266ee0b5e3990020b61b76c"

record CenteredOffExplicitHighBoundary : Set where
  constructor centered-off-explicit-high-boundary
  field
    explicitCenteredCurvatureSourceWritten : Bool
    naturalSignedWindowCutoffSourceWritten : Bool
    explicitFarShellHighUpperSourceWritten : Bool
    finalCenteredOffHighUpperSourceWritten : Bool

    finiteNearPositiveRiskRemains : Bool
    taperDerivativeScalingStillNeededToReadAsDecay : Bool
    positiveMagnitudeUpperIsUniformPrizeClosure : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgda : Bool
    r2ClosedHere : Bool
    rhDerivedHere : Bool

open CenteredOffExplicitHighBoundary public

canonicalCenteredOffExplicitHighBoundary : CenteredOffExplicitHighBoundary
canonicalCenteredOffExplicitHighBoundary =
  centered-off-explicit-high-boundary
    true
    true
    true
    true

    false
    true
    false

    false
    false
    false
    false
