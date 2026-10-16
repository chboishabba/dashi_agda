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
--   -> a residual-only finite-frontier compiler
--   -> generic fixed-word affine threshold certificates
--   -> arbitrary trailing-even certificate extension
--   -> attribution-safe current SOTA atlas
--   -> exact paradoxical-prefix correction seam
--   -> exact coefficient-resonance coordinate
--   -> every contracting word gets canonical threshold A(w)+1
--   -> residual word-certificate coverage -> strict-descent frontier
--   -> strictness guard rejecting globally bounded pseudo-frontiers
--   -> coherent all-horizon survivor histories as inverse-limit obstructions
--   -> contracting survivor forces gap*x <= A(w)
--   -> constructive finite-barrier search / explicit Markov extraction seam.
--
-- The residual producer is still theorem-strength.  Finite computation,
-- density decay, spectral mixing, affine cocycles, word surgery, near-resonance
-- classification, or merely negating an inverse-limit history do not by
-- themselves inhabit it.  A supplied finite same-object survivor barrier DOES
-- compile constructively to literal strict descent; global no-infinite-survivor
-- yields only double negation unless the explicit Nat-search Markov socket is
-- separately paid.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.CollatzSyracuseStrictDescentBaseTailExact as BaseTail
import DASHI.Analysis.CollatzSyracuseOddTailReductionExact as OddTail
import DASHI.Analysis.CollatzSyracuseOddOddTailReductionExact as OddOdd
import DASHI.Analysis.CollatzSyracuseOddSurvivorFrontierExact as OddFrontier
import DASHI.Analysis.CollatzSyracuseEarlyCylinderEliminationExact as Early
import DASHI.Analysis.CollatzSyracuseResidualSurvivorFrontierExact as ResidualFrontier
import DASHI.Analysis.CollatzSyracuseUniformWordDescentCertificateExact as WordCert
import DASHI.Analysis.CollatzSyracuseTrailingZeroCertificateExact as ZeroCert
import DASHI.Analysis.CollatzSyracuseSOTA2026Exact as SOTA
import DASHI.Analysis.CollatzSyracuseParadoxicalPrefixExact as Paradox
import DASHI.Analysis.CollatzSyracuseCoefficientResonanceExact as Resonance
import DASHI.Analysis.CollatzSyracuseContractingWordFamilyExact as ContractingFamily
import DASHI.Analysis.CollatzSyracuseResidualWordCertificateFrontierExact as WordFrontier
import DASHI.Analysis.CollatzSyracuseResidualFrontierStrictnessGuardExact as Strictness
import DASHI.Analysis.CollatzSyracuseResidualInverseLimitObstructionExact as Inverse
import DASHI.Analysis.CollatzSyracuseInfiniteSurvivorAffineObstructionExact as SurvivorAffine
import DASHI.Analysis.CollatzSyracuseConstructiveSurvivorExtractionExact as Extract
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
    residualFrontierCompilerPaid : Nat
    uniformWordDescentCertificatePaid : Nat
    trailingZeroCertificateCompilerPaid : Nat
    sotaAttributionAtlasPaid : Nat
    paradoxicalAffineSeamPaid : Nat
    coefficientResonanceCoordinatePaid : Nat
    contractingWordFamilyCompilerPaid : Nat
    residualWordCertificateFrontierPaid : Nat
    residualFrontierStrictnessGuardPaid : Nat
    residualInverseLimitObstructionPaid : Nat
    infiniteSurvivorAffineObstructionPaid : Nat
    affineCorrectionCocyclePaid : Nat
    adjacentCorrectionSwapPaid : Nat
    universalStoppingCompilerPaid : Nat
    terminalCompilersPaid : Nat

    finiteSurvivorBarrierExtractionPaid : Nat
    noInfiniteSurvivorDoubleNegationPaid : Nat
    explicitNatSearchMarkovSocketPaid : Nat

    finiteSearchPromotesUniversalStopping : Nat
    densityPromotesUniversalStopping : Nat
    oldSpectralRelationPromotesUniversalStopping : Nat
    affineWordSurgeryPromotesUniversalStoppingAlone : Nat
    nearResonanceClassificationPromotesUniversalStoppingAlone : Nat
    natSearchMarkovUnconditionallyPaid : Nat

    unboundedResidualProducerPaid : Nat
    unboundedOddFrontierProducerPaid : Nat
    unboundedResidualFrontierProducerPaid : Nat
    universalContractingCorrectionEscapeProducerPaid : Nat
    allStartsFiniteBarrierProducerPaid : Nat
    onlyCriticalOpenLeafIsLiteralResidualElimination : Nat

canonicalTerminalParityMaxCutBoundary : TerminalParityMaxCutBoundary
canonicalTerminalParityMaxCutBoundary =
  terminalParityMaxCutBoundary
    1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
    1 1 1
    0 0 0 0 0 0
    0 0 0 0 0 1

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

residualFrontierCompilerPaid :
  ResidualFrontier.ResidualSurvivorFrontierBoundary.residualFrontierCompilerPaid
    ResidualFrontier.canonicalResidualSurvivorFrontierBoundary
  ≡ 1
residualFrontierCompilerPaid = refl

uniformWordCertificatePaid :
  WordCert.UniformWordDescentCertificateBoundary.uniformThresholdCompilerPaid
    WordCert.canonicalUniformWordDescentCertificateBoundary
  ≡ 1
uniformWordCertificatePaid = refl

trailingZeroCertificatePaid :
  ZeroCert.TrailingZeroCertificateBoundary.arbitraryTrailingZerosCompilerPaid
    ZeroCert.canonicalTrailingZeroCertificateBoundary
  ≡ 1
trailingZeroCertificatePaid = refl

sotaAttributionAtlasPaid :
  SOTA.CollatzSOTA2026Boundary.attributedSourceAtlasPaid
    SOTA.canonicalCollatzSOTA2026Boundary
  ≡ 1
sotaAttributionAtlasPaid = refl

paradoxicalAffineSeamPaid :
  Paradox.ParadoxicalPrefixBoundary.paradoxicalPrefixStartBoundedByCorrectionPaid
    Paradox.canonicalParadoxicalPrefixBoundary
  ≡ 1
paradoxicalAffineSeamPaid = refl

coefficientResonanceCoordinatePaid :
  Resonance.CoefficientResonanceBoundary.exactCoefficientCoordinatePaid
    Resonance.canonicalCoefficientResonanceBoundary
  ≡ 1
coefficientResonanceCoordinatePaid = refl

contractingWordFamilyCompilerPaid :
  ContractingFamily.ContractingWordFamilyBoundary.everyContractingWordGetsUniformCertificate
    ContractingFamily.canonicalContractingWordFamilyBoundary
  ≡ 1
contractingWordFamilyCompilerPaid = refl

residualWordCertificateFrontierPaid :
  WordFrontier.ResidualWordCertificateFrontierBoundary.finiteCertificateCoverageCompilerPaid
    WordFrontier.canonicalResidualWordCertificateFrontierBoundary
  ≡ 1
residualWordCertificateFrontierPaid = refl

residualFrontierStrictnessGuardPaid :
  Strictness.ResidualFrontierStrictnessBoundary.globallyBoundedFrontierRejected
    Strictness.canonicalResidualFrontierStrictnessBoundary
  ≡ 1
residualFrontierStrictnessGuardPaid = refl

residualInverseLimitObstructionPaid :
  Inverse.ResidualInverseLimitBoundary.infiniteHistoryRefutesStrictDescentPaid
    Inverse.canonicalResidualInverseLimitBoundary
  ≡ 1
residualInverseLimitObstructionPaid = refl

infiniteSurvivorAffineObstructionPaid :
  SurvivorAffine.InfiniteSurvivorAffineBoundary.contractingSurvivorCorrectionDominancePaid
    SurvivorAffine.canonicalInfiniteSurvivorAffineBoundary
  ≡ 1
infiniteSurvivorAffineObstructionPaid = refl

finiteSurvivorBarrierExtractionPaid :
  Extract.ConstructiveSurvivorExtractionBoundary.finiteBarrierExtractionPaid
    Extract.canonicalConstructiveSurvivorExtractionBoundary
  ≡ 1
finiteSurvivorBarrierExtractionPaid = refl

noInfiniteSurvivorDoubleNegationPaid :
  Extract.ConstructiveSurvivorExtractionBoundary.noInfiniteGivesDoubleNegatedDescentPaid
    Extract.canonicalConstructiveSurvivorExtractionBoundary
  ≡ 1
noInfiniteSurvivorDoubleNegationPaid = refl

explicitNatSearchMarkovSocketPaid :
  Extract.ConstructiveSurvivorExtractionBoundary.explicitNatSearchMarkovSocketPaid
    Extract.canonicalConstructiveSurvivorExtractionBoundary
  ≡ 1
explicitNatSearchMarkovSocketPaid = refl

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

oddFrontierGrowthStillOpen :
  OddFrontier.OddSurvivorFrontierBoundary.unboundedOddFrontierProducerPaid
    OddFrontier.canonicalOddSurvivorFrontierBoundary
  ≡ 0
oddFrontierGrowthStillOpen = refl

residualFrontierGrowthStillOpen :
  ResidualFrontier.ResidualSurvivorFrontierBoundary.unboundedResidualFrontierProducerPaid
    ResidualFrontier.canonicalResidualSurvivorFrontierBoundary
  ≡ 0
residualFrontierGrowthStillOpen = refl

contractingCorrectionEscapeStillOpen :
  SurvivorAffine.InfiniteSurvivorAffineBoundary.universalContractingCorrectionEscapeProducerPaid
    SurvivorAffine.canonicalInfiniteSurvivorAffineBoundary
  ≡ 0
contractingCorrectionEscapeStillOpen = refl

certificateCoverageDoesNotCreateUnboundedness :
  WordFrontier.ResidualWordCertificateFrontierBoundary.finiteCoverageCreatesUnboundedFrontier
    WordFrontier.canonicalResidualWordCertificateFrontierBoundary
  ≡ 0
certificateCoverageDoesNotCreateUnboundedness = refl

strictnessGuardDoesNotCreateUnboundedness :
  Strictness.ResidualFrontierStrictnessBoundary.finiteCoverageCreatesUnboundedness
    Strictness.canonicalResidualFrontierStrictnessBoundary
  ≡ 0
strictnessGuardDoesNotCreateUnboundedness = refl

inverseLimitAbsenceDoesNotConstructDescent :
  Inverse.ResidualInverseLimitBoundary.noInverseLimitAutomaticallyConstructsDescent
    Inverse.canonicalResidualInverseLimitBoundary
  ≡ 0
inverseLimitAbsenceDoesNotConstructDescent = refl

markovNotSilentlyOwned :
  Extract.ConstructiveSurvivorExtractionBoundary.natSearchMarkovOwnedUnconditionally
    Extract.canonicalConstructiveSurvivorExtractionBoundary
  ≡ 0
markovNotSilentlyOwned = refl

finiteBarrierProducerStillOpen :
  TerminalParityMaxCutBoundary.allStartsFiniteBarrierProducerPaid
    canonicalTerminalParityMaxCutBoundary
  ≡ 0
finiteBarrierProducerStillOpen = refl
