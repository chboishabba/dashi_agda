module DASHI.Analysis.RiemannQuarticSignedPoleFourierTerminalLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannQuarticSignedPoleFourierMassLeanDonorExact as FourierMass

------------------------------------------------------------------------
-- RH QUARTIC FOURIER TERMINAL RECUT
--
-- Lean companion:
--
--   Synthesis/
--     RiemannProjectiveQuarticFourWindowSignedPoleFourierMass.lean
--     RiemannProjectiveQuarticFourWindowSignedPoleFourierTerminal.lean
--
-- The previous Clay-facing terminal proposition used the exact scalar
--
--   1/2 * (Far_W - integral Psi_t(x) mu(x) dx).
--
-- The Fourier-mass donor now proves the exact same-object decomposition
--
--   integral Psi_t mu
--     =
--   128*pi*mu(t)/(t*R*M0) * OriginDet_W
--     + MuVariation_W.
--
-- Therefore the new terminal proposition is
--
--   1/2 * (
--     Far_W
--     - 128*pi*mu(t)/(t*R*M0) * OriginDet_W
--     - MuVariation_W
--   )
--   < terminalMargin.
--
-- Companion Lean proves this interface equivalent to the old Far-minus-mu
-- interface and feeds it into the already-existing fixed-high contradiction
-- compiler.
--
-- This is a REPRESENTATION/CUTSET result.  It does not prove the displayed
-- strict inequality.  The unpaid mathematics is the coupled signed
-- zero-distribution estimate itself.
------------------------------------------------------------------------

record QuarticSignedPoleFourierTerminalReceipt : Set where
  constructor quartic-signed-pole-fourier-terminal-receipt
  field
    repository : String
    branch : String
    massSpecializationPath : String
    terminalPath : String

    massSpecializationCommit : String
    centerDensityCommit : String
    fullLineSplitCommit : String
    terminalRecutCommit : String

open QuarticSignedPoleFourierTerminalReceipt public

currentQuarticSignedPoleFourierTerminalReceipt :
  QuarticSignedPoleFourierTerminalReceipt
currentQuarticSignedPoleFourierTerminalReceipt =
  quartic-signed-pole-fourier-terminal-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-marked-cluster-target-reflection"
    "Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourierMass.lean"
    "Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourierTerminal.lean"

    "0203c40ce5068f6def0e3ac4f91e768b4f58231b"
    "e3f4e2a7b0ad2dd3e5fb183b5aeeb7861a81c7a0"
    "b5c6e5f09225697103aca81ffd724c142ecaa6f5"
    "6ea592da5f8fe8ec86798937bd9ec6d1a178c6ea"

record QuarticSignedPoleFourierTerminalBoundary : Set where
  constructor quartic-signed-pole-fourier-terminal-boundary
  field
    fullLinePsiIntegrabilitySourceWritten : Bool
    fullLineMuVariationIntegrabilitySourceWritten : Bool
    fullLineCenterDensityVariationSplitSourceWritten : Bool
    canonicalHighScalarExplicitOriginVariationNormalFormSourceWritten : Bool

    explicitOriginVariationUniformInterfaceSourceWritten : Bool
    explicitInterfaceEquivalentToFarMinusMuSourceWritten : Bool
    explicitInterfaceCompilesFixedHighContradictionSourceWritten : Bool
    counterexampleForcesExplicitInterfaceFailureSourceWritten : Bool

    separateFarAbsoluteEstimateRequired : Bool
    separateMuAbsoluteEstimateRequired : Bool
    signedFarOriginVariationCancellationPaid : Bool

    leanExactHeadKernelReceiptOwnedHere : Bool
    agdaIndependentlyProvesAnalyticEstimateHere : Bool
    rhDerivedHere : Bool

    fullLineSplitPaid :
      fullLineCenterDensityVariationSplitSourceWritten ≡ true
    explicitNormalFormPaid :
      canonicalHighScalarExplicitOriginVariationNormalFormSourceWritten ≡ true
    terminalRepresentationCutPaid :
      explicitInterfaceEquivalentToFarMinusMuSourceWritten ≡ true
    terminalCompilerWeldPaid :
      explicitInterfaceCompilesFixedHighContradictionSourceWritten ≡ true

    farNotRequiredSeparately :
      separateFarAbsoluteEstimateRequired ≡ false
    muNotRequiredSeparately :
      separateMuAbsoluteEstimateRequired ≡ false
    actualCancellationStillOpen :
      signedFarOriginVariationCancellationPaid ≡ false
    leanKernelReceiptNotClaimed :
      leanExactHeadKernelReceiptOwnedHere ≡ false
    agdaDoesNotInventAnalyticProof :
      agdaIndependentlyProvesAnalyticEstimateHere ≡ false
    rhStillNotDerived :
      rhDerivedHere ≡ false

    exactTerminalScalar : String
    ordinaryMathematicsWall : String
    provenancePolicy : String

open QuarticSignedPoleFourierTerminalBoundary public

canonicalQuarticSignedPoleFourierTerminalBoundary :
  QuarticSignedPoleFourierTerminalBoundary
canonicalQuarticSignedPoleFourierTerminalBoundary =
  quartic-signed-pole-fourier-terminal-boundary
    true true true true
    true true true true
    false false false
    false false false

    refl refl refl refl
    refl refl refl refl refl refl

    "1/2 * (canonicalLiteralFarPairSource - 128*pi*mu(t)/(t*R*M0)*OriginDet_W - fullMuVariation)"
    "Prove the displayed exact signed scalar lies below the terminal quartic margin uniformly on the selected high witness.  This is a coupled discrete-zero / smooth-density theorem; independent absolute control of Far and mu is not the preferred cut."
    "Lean owns the source-written real/Fourier analysis.  Agda records the donor path, exact cutset and unpaid theorem only; it neither reconstructs Fourier inversion nor marks RH derived."

terminalRepresentationDebtIsPaid :
  QuarticSignedPoleFourierTerminalBoundary.explicitInterfaceEquivalentToFarMinusMuSourceWritten
    canonicalQuarticSignedPoleFourierTerminalBoundary ≡ true
terminalRepresentationDebtIsPaid = refl

signedZeroDistributionEstimateRemainsOpen :
  QuarticSignedPoleFourierTerminalBoundary.signedFarOriginVariationCancellationPaid
    canonicalQuarticSignedPoleFourierTerminalBoundary ≡ false
signedZeroDistributionEstimateRemainsOpen = refl

oldSeparateFarMuAbsoluteRouteNotRequired :
  QuarticSignedPoleFourierTerminalBoundary.separateFarAbsoluteEstimateRequired
    canonicalQuarticSignedPoleFourierTerminalBoundary ≡ false
oldSeparateFarMuAbsoluteRouteNotRequired = refl
