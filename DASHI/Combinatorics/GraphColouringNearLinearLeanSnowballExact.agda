module DASHI.Combinatorics.GraphColouringNearLinearLeanSnowballExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- NEAR-LINEAR 4CT IMPLEMENTATION / VERIFICATION SNOWBALL
--
-- This source is an independent implementation/verification repository, not a
-- primary source for the mathematical theorem.  It is retained because it may
-- discharge some implementation-level proof debt without duplicating those
-- checks in Agda.  Its claims remain bounded to the repository's documented
-- machine-checked scope.
------------------------------------------------------------------------

nearLinear4ctReferenceCode : Source.AttributedSource
nearLinear4ctReferenceCode =
  Source.mkNoDOISource
    "near-linear-4ct contributors"
    "External programs and files for the computer checks in The Four Color Theorem with Linearly Many Reducible Configurations and Near-Linear Time Coloring"
    "GitHub: near-linear-4ct/computer-checks"
    "2026"
    "https://github.com/near-linear-4ct/computer-checks"
    (Source.namedSourceKind "reference software repository")
    "authors' reference C++ implementation for the paper computer checks; software provenance only, not an independent proof import"
    Source.publicAttribution

independentLeanPort : Source.AttributedSource
independentLeanPort =
  Source.mkNoDOISource
    "kfl / repository contributors"
    "Near-linear 4CT computer checks -- Rust & Lean ports"
    "GitHub: kfl/4ct-checks-rust-lean"
    "2026"
    "https://github.com/kfl/4ct-checks-rust-lean"
    (Source.namedSourceKind "independent Lean 4 and Rust verification repository")
    "independent reimplementation of the paper's Appendix A checking pseudocode; documented machine-checked scope includes guarded homomorphism totality/soundness and in-range completeness/equivalence to Algorithm A.2.1, while full end-to-end validation also uses the authors' data repositories"
    Source.publicAttribution

nearLinearLeanSnowballAtlas : Source.AttributedSourceAtlas
nearLinearLeanSnowballAtlas =
  Source.mkSourceAtlas
    "near-linear four-colour implementation verification snowball"
    "DASHI.Combinatorics.GraphColouringNearLinearLeanSnowballExact"
    (nearLinear4ctReferenceCode ∷ independentLeanPort ∷ [])
    "software-provenance snowball for the 2026 near-linear Four-Color computer checks; does not promote repository documentation into the full Four-Color theorem"

------------------------------------------------------------------------
-- Proof-debt routing boundary.
------------------------------------------------------------------------

record NearLinearLeanVerificationBoundary : Set where
  constructor nearLinearLeanVerificationBoundary
  field
    referenceComputerChecksLocated : Bool
    independentLeanPortLocated : Bool
    leanHomomorphismKernelMachineChecked : Bool
    fullFourColourTheoremImportedIntoDashi : Bool
    eightThousandTwoHundredConfigurationsReprovedInAgda : Bool
    externalVerificationMayDischargeBoundedProofDebt : Bool
    externalVerificationAutomaticallyPromotesPaperClaim : Bool

canonicalNearLinearLeanVerificationBoundary : NearLinearLeanVerificationBoundary
canonicalNearLinearLeanVerificationBoundary =
  nearLinearLeanVerificationBoundary
    true
    true
    true
    false
    false
    true
    false
