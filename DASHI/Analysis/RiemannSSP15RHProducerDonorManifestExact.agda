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
  "85f10467c453bea93bd8199ed80054b1fb41b46a"

donorFile : String
donorFile =
  "Synthesis/RiemannQuarticBalancedTernaryStencil.lean"

donorBlob : String
donorBlob =
  "138153858e329469048175fcdeeaf75c182078be"

producerCertificateFile : String
producerCertificateFile =
  "Synthesis/RiemannQuarticProducerRoleCertificate.lean"

producerCertificateBlob : String
producerCertificateBlob =
  "cb89ebc956cedd55179042cf63ff2eaf3d44f073"

producerCertificateTheorem : String
producerCertificateTheorem =
  "Synthesis.RiemannQuarticProducerRoleCertificate.canonical_certificate_inhabited"

sourceRoleKernelTheorem : String
sourceRoleKernelTheorem =
  "Synthesis.RiemannQuarticProducerRoleCertificate.primitive_kernel_via_source_roles"

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

sameGraphWeldPR : String
sameGraphWeldPR = "dashi_lean4 PR #33"

sameGraphWeldBranch : String
sameGraphWeldBranch =
  "agent/rh-ssp15-same-graph-weld-20260928"

sameGraphWeldHead : String
sameGraphWeldHead =
  "3fb8061d2ce31a19f64b56ff6d3e0a087e019e9e"

sameGraphWeldTheorem : String
sameGraphWeldTheorem =
  "Integration.RiemannSSP15RHProducerSameGraphWeld.imported_certificate_inhabited"

sameGraphSignedFRACTRANTheorem : String
sameGraphSignedFRACTRANTheorem =
  "Integration.RiemannSSP15RHProducerSameGraphWeld.source_role_to_signed_execution_commutes"

record RiemannSSP15RHProducerDonorBoundary : Set where
  constructor riemann-ssp15-rh-producer-donor-boundary
  field
    donorCommitPinned : Bool
    donorBlobPinned : Bool
    primitiveKernelTheoremLocated : Bool
    sparseShiftTheoremLocated : Bool
    depthFiveBlockTheoremLocated : Bool
    sourceNativeCoordinateTermsLocated : Bool
    sourceNativeProducerCertificateInhabitedOnDonorBranch : Bool
    sourceRoleKernelTheoremLocated : Bool
    contentAddressedVerifierOwned : Bool
    exactHeadVerifierObserved : Bool
    donorImportedIntoCurrentLeanBranch : Bool
    sameGraphWeldSourceWritten : Bool
    sameGraphSignedFRACTRANWeldSourceWritten : Bool
    sameGraphExactHeadKernelObserved : Bool
    sameGraphProducerCertificateInhabited : Bool

canonicalRiemannSSP15RHProducerDonorBoundary :
  RiemannSSP15RHProducerDonorBoundary
canonicalRiemannSSP15RHProducerDonorBoundary =
  riemann-ssp15-rh-producer-donor-boundary
    true true true true true true true true true false false
    true true false false


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


sameGraphWeldSourceWrittenIsTrue :
  RiemannSSP15RHProducerDonorBoundary.sameGraphWeldSourceWritten
    canonicalRiemannSSP15RHProducerDonorBoundary
  ≡ true
sameGraphWeldSourceWrittenIsTrue = refl

sameGraphSignedFRACTRANWeldSourceWrittenIsTrue :
  RiemannSSP15RHProducerDonorBoundary.sameGraphSignedFRACTRANWeldSourceWritten
    canonicalRiemannSSP15RHProducerDonorBoundary
  ≡ true
sameGraphSignedFRACTRANWeldSourceWrittenIsTrue = refl

sameGraphExactHeadKernelObservedIsFalse :
  RiemannSSP15RHProducerDonorBoundary.sameGraphExactHeadKernelObserved
    canonicalRiemannSSP15RHProducerDonorBoundary
  ≡ false
sameGraphExactHeadKernelObservedIsFalse = refl
