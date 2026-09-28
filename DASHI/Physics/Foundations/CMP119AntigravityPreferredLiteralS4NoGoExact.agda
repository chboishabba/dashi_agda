{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityPreferredLiteralS4NoGoExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _≤_)

import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteSourceTrajectoryExact as Source
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalLiteralPlaquetteHistoryExact as CanonicalHistory
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowALiteralTerminalHistoryExact as CanonicalTerminal
import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteBetaDrivenDensityExact as LiteralDensity
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2Convention
import DASHI.Physics.Foundations.CMP119AntigravityUnitCouplingCapInverseThresholdExact as Unit
import DASHI.Physics.Foundations.CMP119AntigravityPhysicalSU2ThresholdBelowHistoryExact as Threshold
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as Embed
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- PREFERRED LITERAL S4 NO-GO OBJECT
--
-- No free trajectory, split, beta history, history gamma, repository cap,
-- P3 recursion, or pi-normalization object remains.
--
-- All are constructed from:
--   literal plaquette producer
--   + UV chain coherence
--   + literal per-step beta certificates
--   + canonical Row-A threshold
--   + terminal inverse-square data
--   + the beta-driven CMP122 density
--   + the selected Lorentzian trace/F^2 boundary.
------------------------------------------------------------------------

record PreferredLiteralS4NoGo
    (plaquette : Plaquette.PhysicalRunningCouplingData Nat)
    (coherence : Source.LiteralPlaquetteUVChainCoherence plaquette)
    (source :
      CanonicalHistory.CanonicalLiteralPlaquetteHistory plaquette coherence)
    (rowA : RowA.FiniteQuarticResponseConstants)
    (terminal :
      CanonicalTerminal.CanonicalRowALiteralTerminalHistory
        plaquette coherence source rowA) : Set₂ where
  field
    density :
      LiteralDensity.LiteralPlaquetteBetaDrivenDensity
        plaquette
        (CanonicalHistory.trajectory coherence)
        (CanonicalHistory.asLiteralPlaquetteCMP109FiniteHistory source)
        (CanonicalTerminal.asLiteralPlaquetteTerminalHistory terminal)

    traceBoundary :
      SU2Convention.CanonicalBishopSU2TraceBoundary

open PreferredLiteralS4NoGo public

betaDrivenInputs :
  ∀ {plaquette coherence source rowA terminal} →
  PreferredLiteralS4NoGo plaquette coherence source rowA terminal →
  Beta.BetaDrivenCompleteDensityInputs
    {trajectory = CanonicalHistory.trajectory coherence}
    {split =
      DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteTerminalHistoryExact.compiledSplit
        (CanonicalHistory.asLiteralPlaquetteCMP109FiniteHistory source)}
betaDrivenInputs package =
  LiteralDensity.asBetaDrivenCompleteDensityInputs
    (density package)

betaHistoryIsCanonicalLiteralTerminal :
  ∀ {plaquette coherence source rowA terminal}
    (package :
      PreferredLiteralS4NoGo plaquette coherence source rowA terminal) →
  Beta.betaHistory (betaDrivenInputs package)
  ≡
  DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteTerminalHistoryExact.asBetaSplitInverseSquareTerminalHistory
    (CanonicalTerminal.asLiteralPlaquetteTerminalHistory terminal)
betaHistoryIsCanonicalLiteralTerminal package = refl

canonicalGammaAtMostOne :
  ∀ {plaquette coherence source rowA terminal} →
  PreferredLiteralS4NoGo plaquette coherence source rowA terminal →
  RowA.canonicalQuarticResponseGamma rowA ≤ 1ℚ
canonicalGammaAtMostOne {rowA = rowA} package =
  RowA.canonicalQuarticResponseGammaAtMostOne rowA

sameHistoryInverseThresholdAtLeastOne :
  ∀ {plaquette coherence source rowA terminal}
    (package :
      PreferredLiteralS4NoGo plaquette coherence source rowA terminal) →
  1ℚ ≤ CanonicalTerminal.inverseThreshold terminal
sameHistoryInverseThresholdAtLeastOne
    {rowA = rowA} {terminal = terminal} package =
  Unit.inverseThresholdAtLeastOneFromUnitCap
    (CanonicalTerminal.gammaPositive terminal)
    (canonicalGammaAtMostOne package)
    (CanonicalTerminal.inverseThresholdRepresentation terminal)

physicalSU2ThresholdBelowLiteralInverseThreshold :
  ∀ {plaquette coherence source rowA terminal}
    (package :
      PreferredLiteralS4NoGo plaquette coherence source rowA terminal) →
  Bishop._≤_
    Threshold.physicalSU2NoGoThreshold
    (Embed.embed (CanonicalTerminal.inverseThreshold terminal))
physicalSU2ThresholdBelowLiteralInverseThreshold package =
  Threshold.historyAtLeastOneDominatesPhysicalSU2Threshold
    (sameHistoryInverseThresholdAtLeastOne package)

freeTrajectoryRequired : Bool
freeTrajectoryRequired = false

freeBetaSplitRequired : Bool
freeBetaSplitRequired = false

freeBetaHistoryRequired : Bool
freeBetaHistoryRequired = false

freeHistoryGammaRequired : Bool
freeHistoryGammaRequired = false

p3RecursionRequired : Bool
p3RecursionRequired = false

postHocPiConventionEqualityRequired : Bool
postHocPiConventionEqualityRequired = false

freeTrajectoryRequiredIsFalse :
  freeTrajectoryRequired ≡ false
freeTrajectoryRequiredIsFalse = refl

freeBetaSplitRequiredIsFalse :
  freeBetaSplitRequired ≡ false
freeBetaSplitRequiredIsFalse = refl

freeBetaHistoryRequiredIsFalse :
  freeBetaHistoryRequired ≡ false
freeBetaHistoryRequiredIsFalse = refl

freeHistoryGammaRequiredIsFalse :
  freeHistoryGammaRequired ≡ false
freeHistoryGammaRequiredIsFalse = refl

p3RecursionRequiredIsFalse :
  p3RecursionRequired ≡ false
p3RecursionRequiredIsFalse = refl

postHocPiConventionEqualityRequiredIsFalse :
  postHocPiConventionEqualityRequired ≡ false
postHocPiConventionEqualityRequiredIsFalse = refl

preferredLiteralS4NoGoCompilerLevel : ProofLevel
preferredLiteralS4NoGoCompilerLevel = machineChecked
