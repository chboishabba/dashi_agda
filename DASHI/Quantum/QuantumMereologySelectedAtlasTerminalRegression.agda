{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologySelectedAtlasTerminalRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Quantum.QuantumMereologyHeterogeneousFiniteAtlasAuthorityExact as Atlas
import DASHI.Quantum.QuantumMereologyGTPSShortTime2026AuthorityExact as GTPS
import DASHI.Quantum.QuantumMereologySelectedAtlasTerminalMaxCutExact as Terminal

heterogeneous-canonical-pair-charts-source-written :
  Atlas.HeterogeneousCanonicalPairChartsSourceWritten
    Atlas.canonicalHeterogeneousFiniteAtlasStatus ≡ true
heterogeneous-canonical-pair-charts-source-written =
  Atlas.HeterogeneousCanonicalPairChartsSourceWrittenIsTrue
    Atlas.canonicalHeterogeneousFiniteAtlasStatus

arbitrary-finite-subset-marginals-source-written :
  Atlas.ArbitraryFiniteSubsetMarginalsSourceWritten
    Atlas.canonicalHeterogeneousFiniteAtlasStatus ≡ true
arbitrary-finite-subset-marginals-source-written =
  Atlas.ArbitraryFiniteSubsetMarginalsSourceWrittenIsTrue
    Atlas.canonicalHeterogeneousFiniteAtlasStatus

nested-marginal-coherence-remains-open :
  Atlas.NestedMarginalCoherenceSourceWritten
    Atlas.canonicalHeterogeneousFiniteAtlasStatus ≡ false
nested-marginal-coherence-remains-open =
  Atlas.NestedMarginalCoherenceSourceWrittenIsFalse
    Atlas.canonicalHeterogeneousFiniteAtlasStatus

source-gtps-short-time-formula-recorded :
  GTPS.SourceShortTimeSquaredFunctionalSourceWritten
    GTPS.canonicalGTPSShortTimeStatus ≡ true
source-gtps-short-time-formula-recorded =
  GTPS.SourceShortTimeSquaredFunctionalSourceWrittenIsTrue
    GTPS.canonicalGTPSShortTimeStatus

source-projector-production-remains-open :
  GTPS.SourceProjectorAutomaticallyAvailable
    GTPS.canonicalGTPSShortTimeStatus ≡ false
source-projector-production-remains-open =
  GTPS.SourceProjectorAutomaticallyAvailableIsFalse
    GTPS.canonicalGTPSShortTimeStatus

same-state-holographic-weld-remains-open :
  Terminal.SameStateHolographicWeldPaid
    Terminal.canonicalSelectedAtlasTerminalStatus ≡ false
same-state-holographic-weld-remains-open =
  Terminal.SameStateHolographicWeldPaidIsFalse
    Terminal.canonicalSelectedAtlasTerminalStatus
