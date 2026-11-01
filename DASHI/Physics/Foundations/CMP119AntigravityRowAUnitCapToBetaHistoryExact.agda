{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRowAUnitCapToBetaHistoryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (1ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Foundations.CMP119AntigravityBetaHistoryUnitCapBridgeExact as Bridge
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCanonicalYM4StateExact as Canonical
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaFlow
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4RGInvariantRegionPhysicalGapExact as RG
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as Quartic

------------------------------------------------------------------------
-- AG-S4a / ROW-A CANONICAL CAP -> ACTUAL BETA-HISTORY UNIT CAP
--
-- The Row-A quartic-response producer already proves its canonical cap <= 1.
-- The only source-specific equality needed here is that the repository region
-- parameter used by the SAME beta-driven CMP119 state chooses that exact cap.
------------------------------------------------------------------------

record RowACapIsRepositoryCap
    (rowA : Quartic.FiniteQuarticResponseConstants)
    (parameters : RG.YM4RGRegionParameters) : Set where
  field
    repositoryCouplingCapIsRowACap :
      RG.couplingCap parameters
      ≡ Quartic.canonicalQuarticResponseGamma rowA

open RowACapIsRepositoryCap public

rowACapGivesUnitBoundedRegion :
  ∀ rowA parameters →
  RowACapIsRepositoryCap rowA parameters →
  Bridge.UnitBoundedYM4RegionParameters parameters
rowACapGivesUnitBoundedRegion rowA parameters weld = record
  { Bridge.UnitBoundedYM4RegionParameters.couplingCapAtMostOne =
      subst
        (_≤ 1ℚ)
        (repositoryCouplingCapIsRowACap weld)
        (Quartic.canonicalQuarticResponseGammaAtMostOne rowA)
  }

sameBetaHistoryRowACapAtMostOne :
  ∀ {trajectory split inputs parameters}
    (coordinates :
      Canonical.BetaDrivenCanonicalSection2Coordinates
        {trajectory = trajectory} {split = split}
        inputs parameters)
    (rowA : Quartic.FiniteQuarticResponseConstants) →
    RowACapIsRepositoryCap rowA parameters →
  History.gamma (BetaFlow.betaHistory inputs) ≤ 1ℚ
sameBetaHistoryRowACapAtMostOne
    coordinates rowA weld =
  Bridge.betaDrivenHistoryGammaAtMostOne
    coordinates
    (rowACapGivesUnitBoundedRegion rowA _ weld)

rowACapUnitBoundCompilerClosed : Bool
rowACapUnitBoundCompilerClosed = true

repositoryCapIsSameRowACapEqualityStillRequired : Bool
repositoryCapIsSameRowACapEqualityStillRequired = true

rowACapUnitBoundCompilerClosedIsTrue :
  rowACapUnitBoundCompilerClosed ≡ true
rowACapUnitBoundCompilerClosedIsTrue = refl

repositoryCapIsSameRowACapEqualityStillRequiredIsTrue :
  repositoryCapIsSameRowACapEqualityStillRequired ≡ true
repositoryCapIsSameRowACapEqualityStillRequiredIsTrue = refl
