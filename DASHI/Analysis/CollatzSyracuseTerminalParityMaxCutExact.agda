module DASHI.Analysis.CollatzSyracuseTerminalParityMaxCutExact where

------------------------------------------------------------------------
-- REFINED TERMINAL PARITY MAX-CUT
--
-- This owner records the strongest current literal-Syracuse cut without
-- rewriting the older coarse all-start audit.  The paid chain is:
--
--   finite base 2..8
--   -> every even tail start
--   -> every odd/even prefix (10)
--   -> exact early leaves 1100, 11010, 11100
--   -> three residual literal prefix families 11011, 11101, 1111...
--
-- The residual producer is still theorem-strength.  Finite computation,
-- density decay, spectral mixing, affine cocycles, or word surgery do not by
-- themselves inhabit it.  They may only feed a same-object residual/frontier
-- producer whose unboundedness is proved separately.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.CollatzSyracuseStrictDescentBaseTailExact as BaseTail
import DASHI.Analysis.CollatzSyracuseOddTailReductionExact as OddTail
import DASHI.Analysis.CollatzSyracuseOddOddTailReductionExact as OddOdd
import DASHI.Analysis.CollatzSyracuseOddSurvivorFrontierExact as OddFrontier
import DASHI.Analysis.CollatzSyracuseEarlyCylinderEliminationExact as Early
import DASHI.Analysis.CollatzSyracuseAffineCorrectionCocycleExact as Cocycle
import DASHI.Analysis.CollatzSyracuseAffineCorrectionSwapExact as Swap
import DASHI.Analysis.CollatzSyracuseUniversalStoppingCompilerExact as Universal

record TerminalParityMaxCutBoundary : Set where
  constructor terminalParityMaxCutBoundary
  field
    literalFiniteBasePaid : Nat
    evenTailPaid : Nat
    oddEvenPrefixPaid : Nat
    prefix1100Paid : Nat
    prefix11010Paid : Nat
    prefix11100Paid : Nat
    residualThreeCylinderCompilerPaid : Nat
    oddFrontierCompilerPaid : Nat
    affineCorrectionCocyclePaid : Nat
    adjacentCorrectionSwapPaid : Nat
    universalStoppingCompilerPaid : Nat
    terminalCompilersPaid : Nat

    finiteSearchPromotesUniversalStopping : Nat
    densityPromotesUniversalStopping : Nat
    oldSpectralRelationPromotesUniversalStopping : Nat
    affineWordSurgeryPromotesUniversalStoppingAlone : Nat

    unboundedResidualProducerPaid : Nat
    unboundedOddFrontierProducerPaid : Nat
    onlyCriticalOpenLeafIsLiteralResidualElimination : Nat

canonicalTerminalParityMaxCutBoundary : TerminalParityMaxCutBoundary
canonicalTerminalParityMaxCutBoundary =
  terminalParityMaxCutBoundary
    1 1 1 1 1 1 1 1 1 1 1 1
    0 0 0 0
    0 0 1

finiteBasePaid :
  BaseTail.StrictDescentBaseTailBoundary.literalSmallBasePaid
    BaseTail.canonicalStrictDescentBaseTailBoundary
  ≡ 1
finiteBasePaid = refl

evenTailPaid :
  OddTail.OddTailReductionBoundary.evenStartsStrictDescentPaid
    OddTail.canonicalOddTailReductionBoundary
  ≡ 1
evenTailPaid = refl

oddEvenPrefixPaid :
  OddOdd.OddOddTailReductionBoundary.oddEvenTwoStepDescentPaid
    OddOdd.canonicalOddOddTailReductionBoundary
  ≡ 1
oddEvenPrefixPaid = refl

earlyResidualCompilerPaid :
  Early.EarlyCylinderEliminationBoundary.residualThreeCylinderCompilerPaid
    Early.canonicalEarlyCylinderEliminationBoundary
  ≡ 1
earlyResidualCompilerPaid = refl

oddFrontierCompilerPaid :
  OddFrontier.OddSurvivorFrontierBoundary.oddFrontierCompilerPaid
    OddFrontier.canonicalOddSurvivorFrontierBoundary
  ≡ 1
oddFrontierCompilerPaid = refl

correctionCocyclePaid :
  Cocycle.AffineCorrectionCocycleBoundary.exactCorrectionCocycleOwned
    Cocycle.canonicalAffineCorrectionCocycleBoundary
  ≡ 1
correctionCocyclePaid = refl

correctionSwapPaid :
  Swap.AffineCorrectionSwapBoundary.exactMixedRadixStepOwned
    Swap.canonicalAffineCorrectionSwapBoundary
  ≡ 1
correctionSwapPaid = refl

stoppingCompilerPaid :
  Universal.UniversalStoppingBoundary.wellFoundedCompilerOwned
    Universal.canonicalUniversalStoppingBoundary
  ≡ 1
stoppingCompilerPaid = refl

residualStillOpen :
  Early.EarlyCylinderEliminationBoundary.residualProducerPaid
    Early.canonicalEarlyCylinderEliminationBoundary
  ≡ 0
residualStillOpen = refl

frontierGrowthStillOpen :
  OddFrontier.OddSurvivorFrontierBoundary.unboundedOddFrontierProducerPaid
    OddFrontier.canonicalOddSurvivorFrontierBoundary
  ≡ 0
frontierGrowthStillOpen = refl
