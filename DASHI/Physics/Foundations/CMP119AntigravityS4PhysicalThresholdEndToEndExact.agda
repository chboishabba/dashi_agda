{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityS4PhysicalThresholdEndToEndExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (1ℚ; _≤_)

import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravityUnitCouplingCapInverseThresholdExact as Unit
import DASHI.Physics.Foundations.CMP119AntigravityRowAUnitCapToBetaHistoryExact as RowA
import DASHI.Physics.Foundations.CMP119AntigravityPhysicalSU2ThresholdBelowHistoryExact as Physical
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCanonicalYM4StateExact as Canonical
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaFlow
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as Quartic
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as Embed

------------------------------------------------------------------------
-- AG-S4 / END-TO-END NUMERICAL NO-GO THRESHOLD COMPILER
--
-- On the SAME beta-driven history:
--
--   repository cap = canonical Row-A cap
--      -> gamma <= 1
--      -> 1 <= u_*
--      -> (11/24) pi^{-2} <= embed(u_*).
--
-- No further scalar inequality analysis remains.
------------------------------------------------------------------------

betaSplitHistoryInverseThresholdAtLeastOne :
  ∀ {trajectory split inputs parameters}
    (coordinates :
      Canonical.BetaDrivenCanonicalSection2Coordinates
        {trajectory = trajectory} {split = split}
        inputs parameters)
    (rowA : Quartic.FiniteQuarticResponseConstants)
    (capWeld : RowA.RowACapIsRepositoryCap rowA parameters) →
  1ℚ ≤
  History.inverseThreshold (BetaFlow.betaHistory inputs)
betaSplitHistoryInverseThresholdAtLeastOne
    coordinates rowA capWeld =
  Unit.inverseThresholdAtLeastOneFromUnitCap
    (History.gammaPositive (BetaFlow.betaHistory inputs))
    (RowA.sameBetaHistoryRowACapAtMostOne coordinates rowA capWeld)
    (History.inverseThresholdRepresentation (BetaFlow.betaHistory inputs))

physicalSU2ThresholdBelowSameBetaHistory :
  ∀ {trajectory split inputs parameters}
    (coordinates :
      Canonical.BetaDrivenCanonicalSection2Coordinates
        {trajectory = trajectory} {split = split}
        inputs parameters)
    (rowA : Quartic.FiniteQuarticResponseConstants)
    (capWeld : RowA.RowACapIsRepositoryCap rowA parameters) →
  Bishop._≤_
    Physical.physicalSU2NoGoThreshold
    (Embed.embed
      (History.inverseThreshold (BetaFlow.betaHistory inputs)))
physicalSU2ThresholdBelowSameBetaHistory
    coordinates rowA capWeld =
  Physical.historyAtLeastOneDominatesPhysicalSU2Threshold
    (betaSplitHistoryInverseThresholdAtLeastOne
      coordinates rowA capWeld)

s4NumericThresholdEndToEndClosed : Bool
s4NumericThresholdEndToEndClosed = true

s4RepositoryCapEqualityStillRequired : Bool
s4RepositoryCapEqualityStillRequired = true

s4SelectedAnomalySameMachinConventionStillRequired : Bool
s4SelectedAnomalySameMachinConventionStillRequired = true

s4NumericThresholdEndToEndClosedIsTrue :
  s4NumericThresholdEndToEndClosed ≡ true
s4NumericThresholdEndToEndClosedIsTrue = refl

s4RepositoryCapEqualityStillRequiredIsTrue :
  s4RepositoryCapEqualityStillRequired ≡ true
s4RepositoryCapEqualityStillRequiredIsTrue = refl

s4SelectedAnomalySameMachinConventionStillRequiredIsTrue :
  s4SelectedAnomalySameMachinConventionStillRequired ≡ true
s4SelectedAnomalySameMachinConventionStillRequiredIsTrue = refl
