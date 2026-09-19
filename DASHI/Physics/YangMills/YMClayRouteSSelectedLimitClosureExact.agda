{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayRouteSSelectedLimitClosureExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanPairwiseEuclideanSemanticsRound310Exact as R310
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound330Exact as R330
import DASHI.Physics.YangMills.BalabanCMP116R281SourceResponseSameObjectRound342Exact as R342

------------------------------------------------------------------------
-- ROUTE-S H2c PARETO RECUT
--
-- Historical canonical-B packaging (R330/R333) asks for:
--
--   SequentialOrderClosure rationalAbsorptionArithmetic
--   + equality between that closure's Converges and T5 scalar convergence
--
-- solely in order to construct R310.RationalUpperOrderClosure.
--
-- The later terminal R387 route does not consume that record.  It consumes
-- only the one proposition actually used by the limit passage:
--
--   SelectedLimitUpperClosure
--
-- i.e. one-sided upper bounds are closed under the already-selected R278/T5
-- rational convergence relation.
--
-- Therefore the stronger shared-closure object and sameConvergence weld are
-- compatibility packaging, not terminal physical leaves.  The selected
-- one-sided closure theorem remains genuine standard analysis unless an actual
-- inhabitant is supplied.
------------------------------------------------------------------------

terminalSelectedLimitClosure :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ} →
  Set
terminalSelectedLimitClosure {dataSet = dataSet} =
  R342.SelectedLimitUpperClosure {dataSet = dataSet}

r310UpperClosureToTerminalSelectedClosure :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ} →
  R310.RationalUpperOrderClosure dataSet →
  R342.SelectedLimitUpperClosure {dataSet = dataSet}
r310UpperClosureToTerminalSelectedClosure closure =
  R310.RationalUpperOrderClosure.upperClosed closure

r330PackagingToTerminalSelectedClosure :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    (closure : R330.RationalSequentialOrderClosure) →
  R330.T5SequentialOrderClosureWeld dataSet closure →
  R342.SelectedLimitUpperClosure {dataSet = dataSet}
r330PackagingToTerminalSelectedClosure closure weld =
  r310UpperClosureToTerminalSelectedClosure
    (R330.toR310RationalUpperOrderClosure closure weld)

------------------------------------------------------------------------
-- Pareto classification.
------------------------------------------------------------------------

terminalRouteRequiresSequentialOrderClosureRecord : Bool
terminalRouteRequiresSequentialOrderClosureRecord = false

terminalRouteRequiresSequentialOrderClosureRecordIsFalse :
  terminalRouteRequiresSequentialOrderClosureRecord ≡ false
terminalRouteRequiresSequentialOrderClosureRecordIsFalse = refl

terminalRouteRequiresSameConvergenceWeld : Bool
terminalRouteRequiresSameConvergenceWeld = false

terminalRouteRequiresSameConvergenceWeldIsFalse :
  terminalRouteRequiresSameConvergenceWeld ≡ false
terminalRouteRequiresSameConvergenceWeldIsFalse = refl

terminalRouteRequiresSelectedLimitUpperClosure : Bool
terminalRouteRequiresSelectedLimitUpperClosure = true

terminalRouteRequiresSelectedLimitUpperClosureIsTrue :
  terminalRouteRequiresSelectedLimitUpperClosure ≡ true
terminalRouteRequiresSelectedLimitUpperClosureIsTrue = refl

selectedLimitClosureIsFreshYMDecayEstimate : Bool
selectedLimitClosureIsFreshYMDecayEstimate = false

selectedLimitClosureIsFreshYMDecayEstimateIsFalse :
  selectedLimitClosureIsFreshYMDecayEstimate ≡ false
selectedLimitClosureIsFreshYMDecayEstimateIsFalse = refl

strongerR330PackagingStillValidCompatibilityRoute : Bool
strongerR330PackagingStillValidCompatibilityRoute = true

strongerR330PackagingStillValidCompatibilityRouteIsTrue :
  strongerR330PackagingStillValidCompatibilityRoute ≡ true
strongerR330PackagingStillValidCompatibilityRouteIsTrue = refl

r330PackagingToTerminalClosureCompilerLevel : ProofLevel
r330PackagingToTerminalClosureCompilerLevel = machineChecked

terminalSelectedLimitClosureAuthorityLevel : ProofLevel
terminalSelectedLimitClosureAuthorityLevel =
  R342.round342SelectedLimitUpperClosureLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
