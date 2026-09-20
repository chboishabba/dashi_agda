module DASHI.Analysis.RiemannG2ProjectiveBaseProfileQuotientLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- PROJECTIVE BASE PROFILE / CONSUMER-SUFFICIENT QUOTIENT
--
-- Companion Lean now proves that the q-only normalized projective Off transform
-- is not intrinsically a three-piece object.  The determinant algebra cancels
-- the centered constants and leaves one physical profile
--
--   P_t(v)
--     = 4 G_t(v)
--         [ A0(r) cos(v/8) - A0(2r) cos(v/16) ],
--
-- with r=t/16.
--
-- Therefore
--
--   Phi_proj(q) = integral P_t(v) cos(qv) dv.
--
-- This is the exact downstream observable consumed by the projective/RvM lane.
-- Since G_t is supported away from v=0, P_t inherits the open gap
--
--   |v| <= 3*pi/4 -> P_t(v)=0,
--
-- and in particular P_t(0)=0.  The existing Fourier-inversion compiler then
-- annihilates a constant spectral density, conditional only on Fourier L1.
--
-- CROSS-POLLINATION NOTE
--
-- The proof architecture is the same certificate schema used in the
-- j-invariant / 369 observer-residual owners:
--
--   * quotient/projection is justified only for the declared consumer;
--   * the residual/fibre is retained rather than silently erased;
--   * same-object transport is explicit;
--   * pattern reuse does not transfer a theorem from the j lane to RH.
--
-- No j-invariant theorem is used as a premise here.
------------------------------------------------------------------------

record ProjectiveBaseProfileQuotientReceipt : Set where
  constructor projective-base-profile-quotient-receipt
  field
    repository : String
    branch : String
    sourcePath : String
    integrandCollapseTheorem : String
    cosineTransformTheorem : String
    supportGapTheorem : String
    fourierZeroModeTheorem : String
    sourceCommit : String
    rootCommit : String

open ProjectiveBaseProfileQuotientReceipt public

currentProjectiveBaseProfileQuotientReceipt :
  ProjectiveBaseProfileQuotientReceipt
currentProjectiveBaseProfileQuotientReceipt =
  projective-base-profile-quotient-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannNormalizedProjectiveBaseProfile.lean"
    "Synthesis.normalizedProjective_base_integrand_collapse"
    "Synthesis.normalizedProjectiveBaseTransform_eq_physicalCosine"
    "Synthesis.normalizedProjectivePhysicalProfile_zero_of_abs_le"
    "Synthesis.normalizedProjectiveComplexProfile_fourier_total_zero"
    "7ae8e7cd0af55f272659069fa90b3ffdfb518f05"
    "ec2c963c75915fcd2578e712e4b7ece5d79175b4"

record ProjectiveBaseProfileQuotientBoundary : Set where
  constructor projective-base-profile-quotient-boundary
  field
    threePieceBaseTransformCollapsedToOneProfile : Bool
    exactProjectiveCosineTransformSourceWritten : Bool
    projectivePhysicalProfileHasOpenZeroModeGap : Bool
    projectiveWholeLineConstantDensityCancellationCompilerSourceWritten : Bool

    j369CertificateSchemaReused : Bool
    j369TheoremTransferredIntoRH : Bool

    projectiveRvMActualCountingAttachmentPaid : Bool
    residualLogShapeBoundPaid : Bool
    cumulativeRvMDiscrepancyPaid : Bool
    uniformNearLineClosurePaid : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgda : Bool
    rhDerivedHere : Bool

open ProjectiveBaseProfileQuotientBoundary public

canonicalProjectiveBaseProfileQuotientBoundary :
  ProjectiveBaseProfileQuotientBoundary
canonicalProjectiveBaseProfileQuotientBoundary =
  projective-base-profile-quotient-boundary
    true
    true
    true
    true

    true
    false

    false
    false
    false
    false

    false
    false
    false

projectiveBaseIsNowOneConsumerObject :
  ProjectiveBaseProfileQuotientBoundary.threePieceBaseTransformCollapsedToOneProfile
    canonicalProjectiveBaseProfileQuotientBoundary ≡ true
projectiveBaseIsNowOneConsumerObject = refl

noJTheoremTransfer :
  ProjectiveBaseProfileQuotientBoundary.j369TheoremTransferredIntoRH
    canonicalProjectiveBaseProfileQuotientBoundary ≡ false
noJTheoremTransfer = refl

projectiveRvMAttachmentStillOpen :
  ProjectiveBaseProfileQuotientBoundary.projectiveRvMActualCountingAttachmentPaid
    canonicalProjectiveBaseProfileQuotientBoundary ≡ false
projectiveRvMAttachmentStillOpen = refl
