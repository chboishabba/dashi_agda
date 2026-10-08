module DASHI.Analysis.CollatzSyracuseTerminalParityMaxCutValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.CollatzSyracuseTerminalParityMaxCutExact as Terminal

terminalInfrastructurePaid :
  Terminal.TerminalParityMaxCutBoundary.terminalCompilersPaid
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 1
terminalInfrastructurePaid = refl

residualProducerOpen :
  Terminal.TerminalParityMaxCutBoundary.unboundedResidualProducerPaid
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 0
residualProducerOpen = refl

noFinitePromotion :
  Terminal.TerminalParityMaxCutBoundary.finiteSearchPromotesUniversalStopping
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 0
noFinitePromotion = refl
