{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityPreferredLiteralS4NoGoExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (1ℚ; _≤_)

import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Constructor
import DASHI.Physics.Foundations.CMP119AntigravityCMP109PlaquetteFiniteHistoryExact as FiniteHistory
import DASHI.Physics.Foundations.CMP119AntigravityCMP109RowATerminalHistoryExact as Terminal
import DASHI.Physics.Foundations.CMP119AntigravityCMP109RowABetaDrivenDensityExact as Density
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2Convention
import DASHI.Physics.Foundations.CMP119AntigravityUnitCouplingCapInverseThresholdExact as Unit
import DASHI.Physics.Foundations.CMP119AntigravityPhysicalSU2ThresholdBelowHistoryExact as Threshold
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as Embed
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- PREFERRED SOURCE-BUILT S4 NO-GO OBJECT
--
-- Primary object: the CMP109 source-normalized inverse-coupling trajectory.
--
-- From it:
--   source beta = literal one-loop + remainder coefficient
--      -> physical plaquette running data (current/next definitionally aligned)
--      -> finite beta split
--      -> canonical Row-A gamma and inverse threshold
--      -> beta-driven CMP122 density
--      -> physical SU(2) no-go threshold.
--
-- No reverse trajectory reconstruction, UV chain coherence, parallel split,
-- parallel history, free history gamma, free inverse threshold, P3 recursion,
-- post-hoc cap equality, or post-hoc pi equality remains.
------------------------------------------------------------------------

record PreferredLiteralS4NoGo
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (weld : Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory)
    (finiteHistory :
      FiniteHistory.CMP109PlaquetteFiniteHistory trajectory weld)
    (rowA : RowA.FiniteQuarticResponseConstants)
    (terminal :
      Terminal.CMP109RowATerminalHistory
        trajectory weld finiteHistory rowA) : Set₂ where
  field
    density :
      Density.CMP109RowABetaDrivenDensity
        trajectory weld finiteHistory rowA terminal

    traceBoundary :
      SU2Convention.CanonicalBishopSU2TraceBoundary

open PreferredLiteralS4NoGo public

betaDrivenInputs :
  ∀ {trajectory weld finiteHistory rowA terminal} →
  PreferredLiteralS4NoGo trajectory weld finiteHistory rowA terminal →
  Beta.BetaDrivenCompleteDensityInputs
    {trajectory = trajectory}
    {split = FiniteHistory.repositoryBetaSplit finiteHistory}
betaDrivenInputs package =
  Density.asBetaDrivenCompleteDensityInputs
    (density package)

betaHistoryIsCanonicalRowATerminal :
  ∀ {trajectory weld finiteHistory rowA terminal}
    (package :
      PreferredLiteralS4NoGo trajectory weld finiteHistory rowA terminal) →
  Beta.betaHistory (betaDrivenInputs package)
  ≡ Terminal.asBetaSplitInverseSquareTerminalHistory terminal
betaHistoryIsCanonicalRowATerminal package = refl

historyGammaIsCanonicalRowA :
  ∀ {trajectory weld finiteHistory rowA terminal}
    (package :
      PreferredLiteralS4NoGo trajectory weld finiteHistory rowA terminal) →
  History.gamma (Beta.betaHistory (betaDrivenInputs package))
  ≡ RowA.canonicalQuarticResponseGamma rowA
historyGammaIsCanonicalRowA package = refl

historyInverseThresholdIsCanonicalReciprocal :
  ∀ {trajectory weld finiteHistory rowA terminal}
    (package :
      PreferredLiteralS4NoGo trajectory weld finiteHistory rowA terminal) →
  History.inverseThreshold (Beta.betaHistory (betaDrivenInputs package))
  ≡ Terminal.inverseThreshold rowA
historyInverseThresholdIsCanonicalReciprocal package = refl

sameHistoryInverseThresholdAtLeastOne :
  ∀ {trajectory weld finiteHistory rowA terminal}
    (package :
      PreferredLiteralS4NoGo trajectory weld finiteHistory rowA terminal) →
  1ℚ ≤ Terminal.inverseThreshold rowA
sameHistoryInverseThresholdAtLeastOne
    {rowA = rowA} {terminal = terminal} package =
  Unit.inverseThresholdAtLeastOneFromUnitCap
    (Terminal.gammaPositive terminal)
    (RowA.canonicalQuarticResponseGammaAtMostOne rowA)
    (Terminal.inverseThresholdRepresentation rowA)

physicalSU2ThresholdBelowLiteralInverseThreshold :
  ∀ {trajectory weld finiteHistory rowA terminal}
    (package :
      PreferredLiteralS4NoGo trajectory weld finiteHistory rowA terminal) →
  Bishop._≤_
    Threshold.physicalSU2NoGoThreshold
    (Embed.embed (Terminal.inverseThreshold rowA))
physicalSU2ThresholdBelowLiteralInverseThreshold package =
  Threshold.historyAtLeastOneDominatesPhysicalSU2Threshold
    (sameHistoryInverseThresholdAtLeastOne package)

reverseTrajectoryConstructionRequired : Bool
reverseTrajectoryConstructionRequired = false

uvChainCoherenceRequiredOnPreferredRoute : Bool
uvChainCoherenceRequiredOnPreferredRoute = false

parallelBetaSplitRequired : Bool
parallelBetaSplitRequired = false

parallelBetaHistoryRequired : Bool
parallelBetaHistoryRequired = false

freeHistoryGammaRequired : Bool
freeHistoryGammaRequired = false

freeInverseThresholdRequired : Bool
freeInverseThresholdRequired = false

p3RecursionRequired : Bool
p3RecursionRequired = false

postHocCapEqualityRequired : Bool
postHocCapEqualityRequired = false

postHocPiEqualityRequired : Bool
postHocPiEqualityRequired = false

sourceBetaCoefficientIdentityStillRequired : Bool
sourceBetaCoefficientIdentityStillRequired = true

literalCouplingInverseSquareStillRequired : Bool
literalCouplingInverseSquareStillRequired = true

terminalThresholdBoundStillRequired : Bool
terminalThresholdBoundStillRequired = true

reverseTrajectoryConstructionRequiredIsFalse :
  reverseTrajectoryConstructionRequired ≡ false
reverseTrajectoryConstructionRequiredIsFalse = refl

uvChainCoherenceRequiredOnPreferredRouteIsFalse :
  uvChainCoherenceRequiredOnPreferredRoute ≡ false
uvChainCoherenceRequiredOnPreferredRouteIsFalse = refl

parallelBetaSplitRequiredIsFalse :
  parallelBetaSplitRequired ≡ false
parallelBetaSplitRequiredIsFalse = refl

parallelBetaHistoryRequiredIsFalse :
  parallelBetaHistoryRequired ≡ false
parallelBetaHistoryRequiredIsFalse = refl

freeHistoryGammaRequiredIsFalse :
  freeHistoryGammaRequired ≡ false
freeHistoryGammaRequiredIsFalse = refl

freeInverseThresholdRequiredIsFalse :
  freeInverseThresholdRequired ≡ false
freeInverseThresholdRequiredIsFalse = refl

p3RecursionRequiredIsFalse :
  p3RecursionRequired ≡ false
p3RecursionRequiredIsFalse = refl

postHocCapEqualityRequiredIsFalse :
  postHocCapEqualityRequired ≡ false
postHocCapEqualityRequiredIsFalse = refl

postHocPiEqualityRequiredIsFalse :
  postHocPiEqualityRequired ≡ false
postHocPiEqualityRequiredIsFalse = refl

sourceBetaCoefficientIdentityStillRequiredIsTrue :
  sourceBetaCoefficientIdentityStillRequired ≡ true
sourceBetaCoefficientIdentityStillRequiredIsTrue = refl

literalCouplingInverseSquareStillRequiredIsTrue :
  literalCouplingInverseSquareStillRequired ≡ true
literalCouplingInverseSquareStillRequiredIsTrue = refl

terminalThresholdBoundStillRequiredIsTrue :
  terminalThresholdBoundStillRequired ≡ true
terminalThresholdBoundStillRequiredIsTrue = refl

preferredLiteralS4NoGoCompilerLevel : ProofLevel
preferredLiteralS4NoGoCompilerLevel = machineChecked
