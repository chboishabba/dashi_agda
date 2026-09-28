module DASHI.Analysis.RiemannSSP15RHProducerDonorManifestExact where

------------------------------------------------------------------------
-- PINNED RH PRODUCER DONOR
--
-- The source-native primitive coefficient kernel is already theorem-bearing on
-- dashi_lean4 PR #22.  It is not imported into the current SSP15 integration
-- branch, so this module records provenance only and does not fabricate a
-- cross-branch proof term.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

donorCommit : String
donorCommit =
  "824f84cddf5cf424c643688c2d24e351795dac07"

donorFile : String
donorFile =
  "Synthesis/RiemannQuarticBalancedTernaryStencil.lean"

donorBlob : String
donorBlob =
  "138153858e329469048175fcdeeaf75c182078be"

primitiveKernelTheorem : String
primitiveKernelTheorem =
  "Synthesis.RiemannQuarticBalancedTernaryStencil.quarticFourAtomic_primitive_integer_kernel"

sparseShiftTheorem : String
sparseShiftTheorem =
  "Synthesis.RiemannQuarticBalancedTernaryStencil.quarticFourAtomic_sparse_shift_kernel"

depthFiveBlockTheorem : String
depthFiveBlockTheorem =
  "Synthesis.RiemannQuarticBalancedTernaryStencil.quarticFourAtomic_depth_five_block_kernel"

poleCoordinateTerm : String
poleCoordinateTerm =
  "quarticFourAtomicHighPoleResidual"

originCoordinateTerm : String
originCoordinateTerm =
  "quarticFourAtomicProjectiveOriginCoordinate"

jCoordinateTerm : String
jCoordinateTerm =
  "quarticFourAtomicJAt ... 2"

targetCoordinateTerm : String
targetCoordinateTerm =
  "quarticFourAtomicTargetStrengthAt"

record RiemannSSP15RHProducerDonorBoundary : Set where
  constructor riemann-ssp15-rh-producer-donor-boundary
  field
    donorCommitPinned : Bool
    donorBlobPinned : Bool
    primitiveKernelTheoremLocated : Bool
    sparseShiftTheoremLocated : Bool
    depthFiveBlockTheoremLocated : Bool
    sourceNativeCoordinateTermsLocated : Bool
    contentAddressedVerifierOwned : Bool
    exactHeadVerifierObserved : Bool
    donorImportedIntoCurrentLeanBranch : Bool
    sameGraphProducerCertificateInhabited : Bool

canonicalRiemannSSP15RHProducerDonorBoundary :
  RiemannSSP15RHProducerDonorBoundary
canonicalRiemannSSP15RHProducerDonorBoundary =
  riemann-ssp15-rh-producer-donor-boundary
    true true true true true true true false false false


donorCommitPinnedIsTrue :
  RiemannSSP15RHProducerDonorBoundary.donorCommitPinned
    canonicalRiemannSSP15RHProducerDonorBoundary
  ≡ true
donorCommitPinnedIsTrue = refl

contentAddressedVerifierOwnedIsTrue :
  RiemannSSP15RHProducerDonorBoundary.contentAddressedVerifierOwned
    canonicalRiemannSSP15RHProducerDonorBoundary
  ≡ true
contentAddressedVerifierOwnedIsTrue = refl

exactHeadVerifierObservedIsFalse :
  RiemannSSP15RHProducerDonorBoundary.exactHeadVerifierObserved
    canonicalRiemannSSP15RHProducerDonorBoundary
  ≡ false
exactHeadVerifierObservedIsFalse = refl

donorImportedIntoCurrentLeanBranchIsFalse :
  RiemannSSP15RHProducerDonorBoundary.donorImportedIntoCurrentLeanBranch
    canonicalRiemannSSP15RHProducerDonorBoundary
  ≡ false
donorImportedIntoCurrentLeanBranchIsFalse = refl
