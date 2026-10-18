{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityA2NodeToUnifiedHistoryExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteSourceTrajectoryExact as Source
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalLiteralPlaquetteHistoryExact as CanonicalHistory
import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteNodeCouplingExact as Node
import DASHI.Physics.Foundations.CMP119AntigravityNodeAlignedCanonicalRowATerminalHistoryExact as Terminal
import DASHI.Physics.Foundations.CMP119AntigravityNodeAlignedBetaDrivenDensityExact as Density
import DASHI.Physics.Foundations.CMP119AntigravityA2NodeCouplingCoordinateExact as A2Node
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanYM4WardQuarticResponseProducerAdapterExact as A2
import DASHI.Physics.YangMills.BalabanYM4QuarticSourceSensitivityBudgetExact as Quartic
import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact as Direct
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionA2HistoryRound137Exact as R137
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- EARLY A2/NODE WELD -> ROUND137 AUTOMATICALLY
--
-- After the node-aligned density compiler,
--
--   History.couplingAt (Beta.betaHistory inputs) j
--
-- is definitionally Node.sourceCoupling j.
--
-- Hence the early A2NodeCouplingCoordinate is exactly the source theorem
-- Round137 wanted, and no post-density same-object assertion remains.
------------------------------------------------------------------------

asUnifiedGeneratedActionA2History :
  ∀ {HistoryCarrier Cell cutoff}
    {present : Present.PresentCutPhysicalSourceInputs HistoryCarrier Cell cutoff}
    {dataSet coherence literalSource nodeCoupling rowA terminal}
    (density :
      Density.NodeAlignedBetaDrivenDensity
        {dataSet = dataSet}
        coherence literalSource nodeCoupling
        {rowA = rowA} terminal)
    (coordinate :
      A2Node.A2NodeCouplingCoordinate present nodeCoupling)
    (actionWeld :
      R132.UnifiedGeneratedActionDensity
        {inputs = Density.asBetaDrivenCompleteDensityInputs density}
        present) →
  R137.UnifiedGeneratedActionA2History actionWeld
asUnifiedGeneratedActionA2History density coordinate actionWeld = record
  { R137.UnifiedGeneratedActionA2History.a2CouplingIsBetaDrivenDensityCoupling =
      λ j j<cutoff →
        trans
          (A2Node.a2CouplingIsSourceNodeCoupling
            coordinate j j<cutoff)
          (sym
            (Density.betaHistoryCouplingIsNodeAlignedSourceCoupling
              density j))
  }
  where
  sym :
    ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

round137IndependentPhysicalCouplingWeldRequired : Agda.Builtin.Bool.Bool
round137IndependentPhysicalCouplingWeldRequired = Agda.Builtin.Bool.false

a2NodeToUnifiedHistoryCompilerLevel : ProofLevel
a2NodeToUnifiedHistoryCompilerLevel = machineChecked
