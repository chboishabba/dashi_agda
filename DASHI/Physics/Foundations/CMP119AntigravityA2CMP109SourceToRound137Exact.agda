{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityA2CMP109SourceToRound137Exact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Foundations.CMP119AntigravityCMP109SourceCouplingCoordinateExact as SourceCoupling
import DASHI.Physics.Foundations.CMP119AntigravityCMP109SourceRowABetaDrivenDensityExact as SourceDensity
import DASHI.Physics.Foundations.CMP119AntigravityA2CMP109SourceCouplingExact as A2Source
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionA2HistoryRound137Exact as R137
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- EARLY SOURCE-COUPLING WELD -> ROUND137
------------------------------------------------------------------------

asUnifiedGeneratedActionA2History :
  ∀ {HistoryCarrier Cell cutoff}
    {present : Present.PresentCutPhysicalSourceInputs HistoryCarrier Cell cutoff}
    {trajectory weld finiteHistory sourceCoupling rowA terminal}
    (density :
      SourceDensity.CMP109SourceRowABetaDrivenDensity
        finiteHistory sourceCoupling rowA terminal)
    (coordinate :
      A2Source.A2CMP109SourceCouplingCoordinate present sourceCoupling)
    (actionWeld :
      R132.UnifiedGeneratedActionDensity
        {inputs = SourceDensity.asBetaDrivenCompleteDensityInputs density}
        present) →
  R137.UnifiedGeneratedActionA2History actionWeld
asUnifiedGeneratedActionA2History density coordinate actionWeld = record
  { R137.UnifiedGeneratedActionA2History.a2CouplingIsBetaDrivenDensityCoupling =
      λ j j<cutoff →
        trans
          (A2Source.a2CouplingIsCMP109SourceCoupling
            coordinate j j<cutoff)
          (sym
            (SourceDensity.betaHistoryCouplingIsCMP109SourceCoupling
              density j))
  }

independentRound137CouplingWeldRequired : Agda.Builtin.Bool.Bool
independentRound137CouplingWeldRequired = Agda.Builtin.Bool.false

a2CMP109SourceToRound137CompilerLevel : ProofLevel
a2CMP109SourceToRound137CompilerLevel = machineChecked
