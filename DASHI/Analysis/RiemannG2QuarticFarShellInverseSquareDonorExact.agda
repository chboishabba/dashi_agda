module DASHI.Analysis.RiemannG2QuarticFarShellInverseSquareDonorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotleExplicitCutoffCarrierLeanReturnExact as Historical
import DASHI.Analysis.RiemannG2CutoffGrowthBidiExact as Growth
import DASHI.Analysis.RiemannG2DirectR2EnvelopeCompilerExact as R2

------------------------------------------------------------------------
-- QUARTIC FAR-SHELL INVERSE-SQUARE DONOR
--
-- The retained checked Lean provenance records the literal far-shell formula
--
--   farShellBound A |t| J
--     = 18*A*log(|t|+4)/J + 72*A/sqrt(J).
--
-- A new domain-neutral Lean source proves that, for A >= 0 and t >= 1, the
-- quartic schedule J=t^4 gives
--
--   18*A*log(t+4)/t^4 + 72*A/sqrt(t^4) <= 144*A/t^2.
--
-- This is exactly the asymptotic scale suggested by the historical 8889 status,
-- but it is NOT yet the final RH far budget: the new Lean theorem still needs
-- kernel certification and same-object attachment to the checked far-shell
-- owner, the literal target height, and the exact Off cutoff.  The quarter-period
-- crossing admission is independent and also remains unpaid.
------------------------------------------------------------------------

historicalFarShell : Historical.ExplicitCutoffCarrierLeanReturn
historicalFarShell = Historical.canonicalExplicitCutoffCarrierLeanReturn

cutoffBoundary : Growth.CutoffGrowthBidiBoundary
cutoffBoundary = Growth.canonicalCutoffGrowthBidiBoundary

r2Boundary : R2.DirectR2EnvelopeCompilerBoundary
r2Boundary = R2.canonicalDirectR2EnvelopeCompilerBoundary

record LeanQuarticFarShellSourceReceipt : Set where
  constructor lean-quartic-far-shell-source-receipt
  field
    repository : String
    branch : String
    regressionPath : String
    sourcePath : String
    logLemmaName : String
    sqrtLemmaName : String
    fullBoundName : String
    redCommit : String
    atomSourceCommit : String
    fullBoundSourceCommit : String
    rootIntegrationCommit : String
open LeanQuarticFarShellSourceReceipt public

currentLeanQuarticFarShellSourceReceipt : LeanQuarticFarShellSourceReceipt
currentLeanQuarticFarShellSourceReceipt =
  lean-quartic-far-shell-source-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannFarShellQuarticCutoffRegression.lean"
    "Synthesis/RiemannFarShellQuarticCutoff.lean"
    "Synthesis.log_add_four_le_four_mul"
    "Synthesis.sqrt_pow_four"
    "Synthesis.farShell_quartic_le_inverseSquare"
    "63e93c1c22ded77a579040186da328f20539539a"
    "3ac9bc8ff5470f75742fc1f43c9f2ece94d2f2c0"
    "b3cc77d0461fe38c3af35a34fd750e85b932c0f6"
    "ab6373838cbabb0def8a888c4e3fc37f4e2d38d2"

record QuarticFarShellInverseSquareBoundary : Set where
  constructor quartic-far-shell-inverse-square-boundary
  field
    historicalExplicitFarShellFormulaRecorded : Bool
    historicalEveryCutoffTheoremRecorded : Bool
    quarticLogAtomLeanSourceWritten : Bool
    quarticSqrtAtomLeanSourceWritten : Bool
    fullInverseSquareLeanSourceWritten : Bool

    leanKernelReceiptObserved : Bool
    sameObjectHistoricalFarShellOwnerLocatedInCurrentLean : Bool
    sameObjectFarShellTransportPaid : Bool
    literalTargetHeightBoundToLeanT : Bool
    literalOffCutoffEqualsQuarticSchedulePaid : Bool
    quarterPeriodCrossingForQuarticSchedulePaid : Bool
    outerOffOrdinateConstantsBoundToDonor : Bool
    directR2EnvelopePaid : Bool
    rhDerived : Bool
open QuarticFarShellInverseSquareBoundary public

canonicalQuarticFarShellInverseSquareBoundary :
  QuarticFarShellInverseSquareBoundary
canonicalQuarticFarShellInverseSquareBoundary =
  quartic-far-shell-inverse-square-boundary
    true true true true true
    false false false false false false false false false

data QuarticFarShellInverseSquareResidual : Set where
  obtainLeanKernelReceipt : QuarticFarShellInverseSquareResidual
  attachToHistoricalFarShellFormula : QuarticFarShellInverseSquareResidual
  bindLiteralTargetHeight : QuarticFarShellInverseSquareResidual
  admitQuarticCutoffOnLiteralPair : QuarticFarShellInverseSquareResidual
  bindOuterOffOrdinateConstants : QuarticFarShellInverseSquareResidual
  feedFarRateIntoDirectR2Envelope : QuarticFarShellInverseSquareResidual

firstQuarticFarShellInverseSquareResidual : QuarticFarShellInverseSquareResidual
firstQuarticFarShellInverseSquareResidual = obtainLeanKernelReceipt
