module DASHI.Cognition.PNF.ContextWaveFibreSelectionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Biology.Levin.MillerTravelingWaveAccessProducerExact as Miller
import DASHI.Biology.Levin.CrossFrequencyEffectiveTopologyExact as CrossFrequency

------------------------------------------------------------------------
-- Exact composition of the proposed producer chain:
--
-- context -> traveling field phase -> cross-frequency gate -> accessible fibre.
--
-- This is a finite mechanistic shape, not a trauma diagnosis or claim that all
-- contextual retrieval is implemented by this physical route.
------------------------------------------------------------------------

data TriggerContext : Set where
  firstControlContext secondControlContext : TriggerContext

contextTick : TriggerContext → Miller.Tick2
contextTick firstControlContext = Miller.firstTick
contextTick secondControlContext = Miller.secondTick

fieldAccess : TriggerContext → Miller.Site2 → Bool
fieldAccess context site =
  Miller.recruitedAt (contextTick context) site

crossFrequencyGate :
  TriggerContext → Miller.Site2 → CrossFrequency.BetaControl
crossFrequencyGate context site =
  CrossFrequency.travelingBetaAt (contextTick context) site

leftAccessibleInFirstContext :
  fieldAccess firstControlContext Miller.leftSite ≡ true
leftAccessibleInFirstContext = refl

leftClosedInSecondContext :
  fieldAccess secondControlContext Miller.leftSite ≡ false
leftClosedInSecondContext = refl

contextChangesAccessibleFibre :
  fieldAccess firstControlContext Miller.leftSite
  ≡ fieldAccess secondControlContext Miller.leftSite → ⊥
contextChangesAccessibleFibre ()

firstContextUsesOpenBetaGate :
  crossFrequencyGate firstControlContext Miller.leftSite
  ≡ CrossFrequency.betaLow
firstContextUsesOpenBetaGate = refl

secondContextUsesClosedBetaGate :
  crossFrequencyGate secondControlContext Miller.leftSite
  ≡ CrossFrequency.betaHigh
secondContextUsesClosedBetaGate = refl

record ContextWaveFibreBoundary : Set where
  constructor contextWaveFibreBoundary
  field
    contextContrastProvesTrauma : Bool
    accessClosureMeansMemoryAbsent : Bool
    waveGateIsSemanticRevision : Bool
    producerChainIsUniversal : Bool

canonicalContextWaveFibreBoundary : ContextWaveFibreBoundary
canonicalContextWaveFibreBoundary =
  contextWaveFibreBoundary false false false false
