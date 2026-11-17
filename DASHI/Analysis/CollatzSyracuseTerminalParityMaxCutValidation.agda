module DASHI.Analysis.CollatzSyracuseTerminalParityMaxCutValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.CollatzSyracuseTerminalParityMaxCutExact as Terminal

terminalInfrastructurePaid :
  Terminal.TerminalParityMaxCutBoundary.terminalCompilersPaid
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 1
terminalInfrastructurePaid = refl

sharpBarrierPaid :
  Terminal.TerminalParityMaxCutBoundary.sharpBarrierThresholdPaid
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 1
sharpBarrierPaid = refl

sharpMinimalityPaid :
  Terminal.TerminalParityMaxCutBoundary.sharpBarrierMinimalityPaid
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 1
sharpMinimalityPaid = refl

prefixTransitionPaid :
  Terminal.TerminalParityMaxCutBoundary.affinePrefixTransitionPaid
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 1
prefixTransitionPaid = refl

safeOddGapPaid :
  Terminal.TerminalParityMaxCutBoundary.safeOddGapProducerPaid
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 1
safeOddGapPaid = refl

trailingEvenSharpBarrierPaid :
  Terminal.TerminalParityMaxCutBoundary.trailingEvenSharpBarrierMonotonicityPaid
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 1
trailingEvenSharpBarrierPaid = refl

finiteBarrierExtractionPaid :
  Terminal.TerminalParityMaxCutBoundary.finiteSurvivorBarrierExtractionPaid
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 1
finiteBarrierExtractionPaid = refl

noInfiniteDoubleNegationPaid :
  Terminal.TerminalParityMaxCutBoundary.noInfiniteSurvivorDoubleNegationPaid
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 1
noInfiniteDoubleNegationPaid = refl

markovStillExplicit :
  Terminal.TerminalParityMaxCutBoundary.natSearchMarkovUnconditionallyPaid
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 0
markovStillExplicit = refl

residualProducerOpen :
  Terminal.TerminalParityMaxCutBoundary.unboundedResidualProducerPaid
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 0
residualProducerOpen = refl

finiteBarrierProducerOpen :
  Terminal.TerminalParityMaxCutBoundary.allStartsFiniteBarrierProducerPaid
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 0
finiteBarrierProducerOpen = refl

noFinitePromotion :
  Terminal.TerminalParityMaxCutBoundary.finiteSearchPromotesUniversalStopping
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 0
noFinitePromotion = refl
