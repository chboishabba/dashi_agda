module DASHI.Analysis.CollatzSyracuseSharpBarrierTerminalMaxCutExact where

------------------------------------------------------------------------
-- SHARP-BARRIER TERMINAL CAPSTONE
--
-- This is the current refinement of the broader terminal parity max-cut.  It
-- records only the new theorem-distance-minimising payments added after the
-- earlier terminal ledger stabilized:
--
--   * exact least threshold N*(w)=floor(A/g)+1;
--   * exact late-bit affine/gap transitions;
--   * late-even and late-10 sharp-barrier nonincrease;
--   * exact internal coefficient-stopping ordering and conditional equality;
--   * exact typed primitive continuation AST with all semantic invariants
--     proof-carrying and AST escape compiling to the canonical escape source;
--   * attribution-safe coefficient-stopping / base-conversion / semiconvergent
--     source roles.
--
-- It deliberately leaves both universal correction escape and universal
-- coefficient-stopping equality unpaid.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.CollatzSyracuseTerminalParityMaxCutExact as Terminal
import DASHI.Analysis.CollatzSyracuseSharpBarrierThresholdExact as Sharp
import DASHI.Analysis.CollatzSyracuseAffinePrefixTransitionExact as Prefix
import DASHI.Analysis.CollatzSyracuseSharpBarrierTransitionExact as EvenBarrier
import DASHI.Analysis.CollatzSyracuseSharpBarrierOneZeroTransitionExact as OneZero
import DASHI.Analysis.CollatzSyracuseSharpBarrierPrimitiveASTExact as AST
import DASHI.Analysis.CollatzSyracuseCoefficientStoppingBoundaryExact as CST
import DASHI.Analysis.CollatzSyracuseSOTA2026Exact as SOTA
import DASHI.Analysis.CollatzSyracuseInfiniteSurvivorAffineObstructionExact as Escape

record SharpBarrierTerminalBoundary : Set where
  constructor sharpBarrierTerminalBoundary
  field
    priorTerminalSpineImported : Nat
    sharpThresholdAndMinimalityPaid : Nat
    exactLateBitTransitionPaid : Nat
    safeOddGapConstructionPaid : Nat
    trailingEvenBarrierLawPaid : Nat
    trailingOneZeroBarrierLawPaid : Nat
    typedPrimitiveASTPaid : Nat
    astEscapeCompilerPaid : Nat
    coefficientStoppingInternalBoundaryPaid : Nat
    coefficientStoppingAttributionPaid : Nat

    universalASTBarrierEscapeProducerPaid : Nat
    universalCorrectionEscapeProducerPaid : Nat
    universalCoefficientStoppingEqualityPaid : Nat
    finiteCoefficientScanPromotesUniversality : Nat
    semiconvergentClassificationPromotesCorrectionEscape : Nat
    baseConversionRepresentationPromotesUniversalStopping : Nat

canonicalSharpBarrierTerminalBoundary : SharpBarrierTerminalBoundary
canonicalSharpBarrierTerminalBoundary =
  sharpBarrierTerminalBoundary
    1 1 1 1 1 1 1 1 1 1
    0 0 0 0 0 0

priorTerminalSpinePaid :
  Terminal.TerminalParityMaxCutBoundary.terminalCompilersPaid
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 1
priorTerminalSpinePaid = refl

sharpThresholdPaid :
  Sharp.SharpBarrierThresholdBoundary.sharpQuotientThresholdPaid
    Sharp.canonicalSharpBarrierThresholdBoundary
  ≡ 1
sharpThresholdPaid = refl

sharpMinimalityPaid :
  Sharp.SharpBarrierThresholdBoundary.sharpThresholdMinimalityPaid
    Sharp.canonicalSharpBarrierThresholdBoundary
  ≡ 1
sharpMinimalityPaid = refl

lateBitTransitionPaid :
  Prefix.AffinePrefixTransitionBoundary.trailingOddTransitionPaid
    Prefix.canonicalAffinePrefixTransitionBoundary
  ≡ 1
lateBitTransitionPaid = refl

safeOddGapConstructionPaid :
  Prefix.AffinePrefixTransitionBoundary.safeOddConditionBuildsNewGapPaid
    Prefix.canonicalAffinePrefixTransitionBoundary
  ≡ 1
safeOddGapConstructionPaid = refl

trailingEvenBarrierPaid :
  EvenBarrier.SharpBarrierTransitionBoundary.arbitraryTrailingEvenSharpThresholdNonincreasingPaid
    EvenBarrier.canonicalSharpBarrierTransitionBoundary
  ≡ 1
trailingEvenBarrierPaid = refl

trailingOneZeroBarrierPaid :
  OneZero.SharpBarrierOneZeroBoundary.trailingOneZeroSharpThresholdNonincreasingPaid
    OneZero.canonicalSharpBarrierOneZeroBoundary
  ≡ 1
trailingOneZeroBarrierPaid = refl

typedPrimitiveASTPaid :
  AST.PrimitiveASTBoundary.typedPrimitiveASTPaid
    AST.canonicalPrimitiveASTBoundary
  ≡ 1
typedPrimitiveASTPaid = refl

astEscapeCompilerPaid :
  AST.PrimitiveASTBoundary.astEscapeCompilesToCanonicalPaid
    AST.canonicalPrimitiveASTBoundary
  ≡ 1
astEscapeCompilerPaid = refl

coefficientStoppingOrderingPaid :
  CST.CoefficientStoppingBoundary.coefficientHorizonAtMostDescentHorizonPaid
    CST.canonicalCoefficientStoppingBoundary
  ≡ 1
coefficientStoppingOrderingPaid = refl

coefficientStoppingConditionalEqualityPaid :
  CST.CoefficientStoppingBoundary.correctionFitAtCoefficientHorizonImpliesEqualityPaid
    CST.canonicalCoefficientStoppingBoundary
  ≡ 1
coefficientStoppingConditionalEqualityPaid = refl

coefficientStoppingSourcesPaid :
  SOTA.CollatzSOTA2026Boundary.coefficientStoppingHistoryAttributed
    SOTA.canonicalCollatzSOTA2026Boundary
  ≡ 1
coefficientStoppingSourcesPaid = refl

universalASTBarrierEscapeStillOpen :
  AST.PrimitiveASTBoundary.universalBarrierEscapeProducerPaid
    AST.canonicalPrimitiveASTBoundary
  ≡ 0
universalASTBarrierEscapeStillOpen = refl

universalCorrectionEscapeStillOpen :
  Escape.InfiniteSurvivorAffineBoundary.universalContractingCorrectionEscapeProducerPaid
    Escape.canonicalInfiniteSurvivorAffineBoundary
  ≡ 0
universalCorrectionEscapeStillOpen = refl

universalCoefficientStoppingStillOpen :
  CST.CoefficientStoppingBoundary.universalCoefficientStoppingEqualityPaid
    CST.canonicalCoefficientStoppingBoundary
  ≡ 0
universalCoefficientStoppingStillOpen = refl
