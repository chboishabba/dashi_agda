module DASHI.Unified.OccupyNonDominationTOEExact where

open import DASHI.Core.Prelude

import DASHI.Governance.OccupyDeclaredRealizedControlExact as Declaration
import DASHI.Governance.BoloBoloOWSSpokesProposalLineageExact as Design
import DASHI.Governance.DeliberativeViableNonDominationLoopExact as Action
import DASHI.Governance.BoloBoloNonDominationObserverSufficiencyExact as Observer
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

-- Source declarations and intended designs do not determine realized control.
-- Both non-factorability proofs belong to their original governance owners.
declarationCannotDetermineRealizedControl :
  Declaration.DeclaredPurposeDeterminesRealizedControl → ⊥
declarationCannotDetermineRealizedControl =
  Declaration.declaredPurposeDoesNotDetermineRealizedControl

designCannotDetermineRealizedControl :
  Design.IntendedDesignDeterminesRealizedControl → ⊥
designCannotDetermineRealizedControl =
  Design.intendedDesignDoesNotDetermineRealizedControl

-- Performance and capacity are insufficient for the separate control consumer.
performanceCannotDetermineRealizedControl :
  Descent.ConsumerSufficient
    Observer.efficiencyCapacityObserver Observer.realizedControlConsumer → ⊥
performanceCannotDetermineRealizedControl =
  Observer.efficiencyCapacityCannotCertifyRealizedControl

-- Retain the existing admitted-action boundary; never synthesize a receipt.
nonDominationActionBoundary : Action.DeliberativeViableNonDominationBoundary
nonDominationActionBoundary = Action.canonicalDeliberativeViableNonDominationBoundary
