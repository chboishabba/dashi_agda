module DASHI.Analysis.RiemannG2NormalizedProjectiveOffAtomicMeasureLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- COMBINED NORMALIZED PROJECTIVE OFF ATOMIC CARRIER
--
-- Companion Lean now packages the exact projective Off observable for one
-- actual reflection pair on a single normalized carrier.
--
-- The projective defect is decomposed as
--
--   ΔC(2r) A0(r) - ΔC(r) A0(2r)
--     + C(0) [A0(r)-A0(2r)],
--
-- and, for the canonical r=t/16 taper, each of the three terms is represented
-- exactly with the same 1/t Jacobian:
--
--   * k=2 centered normalized atom;
--   * k=1 centered normalized atom;
--   * radius-zero normalized atom.
--
-- Lean therefore proves, per actual zero rho,
--
--   literalPairProjectiveDefect rho
--     = (1/t) * normalizedProjectiveOffZeroAtom rho,
--
-- and the corresponding exact finite-sum identity.
--
-- This is stronger than merely knowing that the three ingredients separately
-- have normalized realizations.  It is still NOT the whole literal
-- offOrdProjectiveDefect, whose definition uses the infinite reflection-pair
-- tsum.  The infinite-tsum same-object attachment and signed RvM estimate remain
-- open.
------------------------------------------------------------------------

record NormalizedProjectiveOffAtomicMeasureReceipt : Set where
  constructor normalized-projective-off-atomic-measure-receipt
  field
    repository : String
    branch : String
    sourcePath : String
    unrestrictedPairCenteringTheorem : String
    perPairProjectiveAtomTheorem : String
    finiteProjectiveSumTheorem : String
    sourceCommit : String

open NormalizedProjectiveOffAtomicMeasureReceipt public

currentNormalizedProjectiveOffAtomicMeasureReceipt :
  NormalizedProjectiveOffAtomicMeasureReceipt
currentNormalizedProjectiveOffAtomicMeasureReceipt =
  normalized-projective-off-atomic-measure-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannNormalizedProjectiveOffAtomicMeasure.lean"
    "Synthesis.literalPairRadiusChannel_centered"
    "Synthesis.literalPairProjectiveDefect_eq_one_div_t_mul_normalizedAtom"
    "Synthesis.sum_literalPairProjectiveDefects_eq_normalizedAtoms"
    "ba43e6acde69a953317efd7ce49c8f1faba70ac0"

record NormalizedProjectiveOffAtomicMeasureBoundary : Set where
  constructor normalized-projective-off-atomic-measure-boundary
  field
    unrestrictedLiteralPairCenteringSourceWritten : Bool
    exactPerPairProjectiveNormalizationSourceWritten : Bool
    exactFiniteProjectiveSumNormalizationSourceWritten : Bool

    literalInfiniteProjectiveOffTsumAttachmentPaid : Bool
    signedRvMProjectiveEstimatePaid : Bool
    projectiveOffAnalyticBoundPaid : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgda : Bool
    highAnalyticClosurePaid : Bool
    rhDerivedHere : Bool

open NormalizedProjectiveOffAtomicMeasureBoundary public

canonicalNormalizedProjectiveOffAtomicMeasureBoundary :
  NormalizedProjectiveOffAtomicMeasureBoundary
canonicalNormalizedProjectiveOffAtomicMeasureBoundary =
  normalized-projective-off-atomic-measure-boundary
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

finiteProjectiveAtomicCarrierNowSingleObject :
  NormalizedProjectiveOffAtomicMeasureBoundary.exactPerPairProjectiveNormalizationSourceWritten
    canonicalNormalizedProjectiveOffAtomicMeasureBoundary ≡ true
finiteProjectiveAtomicCarrierNowSingleObject = refl

infiniteProjectiveTsumAttachmentStillOpen :
  NormalizedProjectiveOffAtomicMeasureBoundary.literalInfiniteProjectiveOffTsumAttachmentPaid
    canonicalNormalizedProjectiveOffAtomicMeasureBoundary ≡ false
infiniteProjectiveTsumAttachmentStillOpen = refl
