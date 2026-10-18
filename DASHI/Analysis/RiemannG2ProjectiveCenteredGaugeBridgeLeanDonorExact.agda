module DASHI.Analysis.RiemannG2ProjectiveCenteredGaugeBridgeLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- PROJECTIVE / CENTERED SAME-OBJECT BRIDGE
--
-- The live reflection-pair signed cutset consumes the two-radius projective
-- defect
--
--   D_C(r) = C(2r) A0(r) - C(r) A0(2r),
--
-- whereas the normalized Fourier/RvM machinery is naturally stated for
-- radius-centered differences C(s)-C(0).
--
-- Companion Lean now proves the exact projective gauge invariance
--
--   D_{C-c A0}(r) = D_C(r)
--
-- for every scalar c.  If A0(0) != 0, choosing
--
--   c = C(0)/A0(0)
--
-- makes the gauged channel vanish at radius zero and rewrites its values as
--
--   [C(s)-C(0)] - c [A0(s)-A0(0)].
--
-- Therefore the literal projective Off defect is reconstructed exactly from
-- the centered Off differences at r and 2r plus the centered on-line profile.
-- No balance theorem and no absolute-value estimate enter this bridge.
--
-- This prevents the one-radius centered/RvM observable from being silently
-- identified with the projective consumer.
------------------------------------------------------------------------

record ProjectiveCenteredGaugeBridgeReceipt : Set where
  constructor projective-centered-gauge-bridge-receipt
  field
    repository : String
    branch : String
    sourcePath : String
    gaugeInvariantTheorem : String
    centeredReconstructionTheorem : String
    literalOffSpecializationTheorem : String
    sourceCommit : String

open ProjectiveCenteredGaugeBridgeReceipt public

currentProjectiveCenteredGaugeBridgeReceipt :
  ProjectiveCenteredGaugeBridgeReceipt
currentProjectiveCenteredGaugeBridgeReceipt =
  projective-centered-gauge-bridge-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannProjectiveCenteredGaugeBridge.lean"
    "Synthesis.channelProjectiveDefect_projectiveGauge"
    "Synthesis.channelProjectiveDefect_eq_centeredGauge"
    "Synthesis.offOrdProjectiveDefect_eq_centeredGauge"
    "cbdb5537066b29fad5caa34c0439e3810471854f"

record ProjectiveCenteredGaugeBridgeBoundary : Set where
  constructor projective-centered-gauge-bridge-boundary
  field
    projectiveGaugeInvarianceSourceWritten : Bool
    radiusZeroGaugeSourceWritten : Bool
    centeredTwoRadiusReconstructionSourceWritten : Bool
    literalOffSpecializationSourceWritten : Bool

    oneRadiusCenteredObservableDefinitionallyProjective : Bool
    secondRadiusCenteredNormalizedAttachmentPaid : Bool
    normalizedRvMProjectiveConsumerFullyAttached : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgda : Bool
    highAnalyticClosurePaid : Bool
    rhDerivedHere : Bool

open ProjectiveCenteredGaugeBridgeBoundary public

canonicalProjectiveCenteredGaugeBridgeBoundary :
  ProjectiveCenteredGaugeBridgeBoundary
canonicalProjectiveCenteredGaugeBridgeBoundary =
  projective-centered-gauge-bridge-boundary
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

centeredAndProjectiveNotDefinitionallySame :
  ProjectiveCenteredGaugeBridgeBoundary.oneRadiusCenteredObservableDefinitionallyProjective
    canonicalProjectiveCenteredGaugeBridgeBoundary ≡ false
centeredAndProjectiveNotDefinitionallySame = refl

exactTwoRadiusGaugeBridgePaid :
  ProjectiveCenteredGaugeBridgeBoundary.centeredTwoRadiusReconstructionSourceWritten
    canonicalProjectiveCenteredGaugeBridgeBoundary ≡ true
exactTwoRadiusGaugeBridgePaid = refl
