module DASHI.Analysis.RiemannG2PhaseSensitiveRuntimeDiagnosticExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- PHASE-SENSITIVE FINITE-NEAR RUNTIME DIAGNOSTIC
--
-- Execute the consumer-sufficient one-sided idea numerically without confusing
-- it with the still-unpaid same-object pole-quotient theorem.
--
-- Diagnostic cell architecture:
--
--   4 * g(u) * cosh(alpha*u) * cos(delta*u)
--
-- with a deliberately non-authoritative Gaussian g.  Actual Riemann-zero
-- ordinates are used only to generate target-relative phase gaps delta.  The
-- one-sided majorant is
--
--   4*g*cosh(alpha*u)*max(cos(delta*u),0),
--
-- which is pointwise >= the signed cell integrand whenever the envelope is
-- nonnegative.  This exercises the PhaseWeldCellwiseUpperBridge mechanism but
-- does not instantiate the final universal pole-quotient taper or an off-line
-- zero carrier.
------------------------------------------------------------------------

record PhaseSensitiveRuntimeReceipt : Set where
  constructor phase-sensitive-runtime-receipt
  field
    repository : String
    branch : String
    scriptPath : String
    scriptGitBlob : String
    executedScriptSHA256 : String
    outputPath : String
    outputSHA256 : String
    testedCells : Nat
    targetZeroIndex : Nat
    allOneSidedBoundsHeld : Bool
    actualRiemannZeroOrdinatesUsedForPhaseGaps : Bool
    gaussianDiagnosticTaperUsed : Bool
    sameObjectUniversalPoleQuotientTaperUsed : Bool
    phaseSensitiveUpperStrictlyBelowCoarseOnAllTestedCells : Bool
    minimumPhaseOverCoarsePermille : Nat
    medianPhaseOverCoarsePermille : Nat
    maximumPhaseOverCoarsePermille : Nat
    exactLocalRuntimeExecuted : Bool
    scriptCommittedToRepository : Bool
    outputCommittedToRepository : Bool
open PhaseSensitiveRuntimeReceipt public

currentPhaseSensitiveRuntimeReceipt : PhaseSensitiveRuntimeReceipt
currentPhaseSensitiveRuntimeReceipt =
  phase-sensitive-runtime-receipt
    "chboishabba/dashi_agda"
    "agent/rsa260-bidi-projection-freeze-observer-packet"
    "scripts/riemann_g2_phase_sensitive_near_diagnostic.py"
    "eae1b579f5472bdce5cd3cd940daae4e7c71a5bf"
    "770e415d211df12e3682fa3540ca7e78eafd75dd72b1c260846f78554f48391f"
    "/mnt/data/riemann_g2_phase_sensitive_near_diagnostic.json"
    "1082cc182725de4b84e38216c0ce311ebbefa59eefe9a420d403515dd9c094b5"
    18
    9
    true
    true
    true
    false
    true
    311
    341
    741
    true
    true
    false

record PhaseSensitiveRuntimeDiagnosticBoundary : Set where
  constructor phase-sensitive-runtime-diagnostic-boundary
  field
    literalFourGCoshCosArchitectureExercised : Bool
    phaseSensitiveOneSidedMajorantExercised : Bool
    allEighteenNumericalBoundsHeld : Bool
    phaseSensitiveUpperMateriallyBelowCoarseEnvelopeInRun : Bool
    runtimeUsesActualRiemannZeroOrdinatesForPhaseGaps : Bool
    runtimeUsesFinalUniversalPoleQuotientTaper : Bool
    runtimeUsesAuthenticatedOffLineZeroCarrier : Bool
    runtimePaysSameObjectPhaseWeld : Bool
    runtimePaysFiniteNearTheorem : Bool
    runtimePaysStrictNearFarMargin : Bool
    runtimeProvesRH : Bool
open PhaseSensitiveRuntimeDiagnosticBoundary public

canonicalPhaseSensitiveRuntimeDiagnosticBoundary :
  PhaseSensitiveRuntimeDiagnosticBoundary
canonicalPhaseSensitiveRuntimeDiagnosticBoundary =
  phase-sensitive-runtime-diagnostic-boundary
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

data PhaseSensitiveRuntimeResidual : Set where
  replaceGaussianWithExactUniversalPoleQuotientTaper : PhaseSensitiveRuntimeResidual
  bindSameObjectLiteralPhaseCarrier : PhaseSensitiveRuntimeResidual
  turnNumericalMajorantIntoProofCarryingCellUpper : PhaseSensitiveRuntimeResidual
  instantiateExactFiniteNearEnumeration : PhaseSensitiveRuntimeResidual
  compareCertifiedNearUpperAgainstOwnedFarShell : PhaseSensitiveRuntimeResidual

firstPhaseSensitiveRuntimeResidual : PhaseSensitiveRuntimeResidual
firstPhaseSensitiveRuntimeResidual = replaceGaussianWithExactUniversalPoleQuotientTaper
