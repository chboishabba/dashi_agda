{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityBetaHistoryUnitCapBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (1ℚ; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCanonicalYM4StateExact as Canonical
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaFlow
import DASHI.Physics.YangMills.BalabanYM4RGInvariantRegionPhysicalGapExact as RG

------------------------------------------------------------------------
-- AG-S4a / ACTUAL BETA HISTORY gamma <= REPOSITORY CAP <= 1
--
-- The canonical beta-driven state already owns
--
--   History.gamma(betaHistory inputs) <= RG.couplingCap parameters.
--
-- Therefore the only extra scalar fact needed to obtain gamma <= 1 is that
-- this SAME repository parameter package uses a unit-bounded coupling cap.
------------------------------------------------------------------------

record UnitBoundedYM4RegionParameters
    (parameters : RG.YM4RGRegionParameters) : Set where
  field
    couplingCapAtMostOne :
      RG.couplingCap parameters ≤ 1ℚ

open UnitBoundedYM4RegionParameters public

betaDrivenHistoryGammaAtMostOne :
  ∀ {trajectory split inputs parameters}
    (coordinates :
      Canonical.BetaDrivenCanonicalSection2Coordinates
        {trajectory = trajectory} {split = split}
        inputs parameters) →
    UnitBoundedYM4RegionParameters parameters →
  History.gamma (BetaFlow.betaHistory inputs) ≤ 1ℚ
betaDrivenHistoryGammaAtMostOne coordinates bounded =
  ℚP.≤-trans
    (Canonical.gammaInsideRepositoryCap coordinates)
    (couplingCapAtMostOne bounded)

s4HistoryGammaSameObjectUnitCapCompilerClosed : Bool
s4HistoryGammaSameObjectUnitCapCompilerClosed = true

s4RepositoryCouplingCapAtMostOneStillRequired : Bool
s4RepositoryCouplingCapAtMostOneStillRequired = true

s4HistoryGammaSameObjectUnitCapCompilerClosedIsTrue :
  s4HistoryGammaSameObjectUnitCapCompilerClosed ≡ true
s4HistoryGammaSameObjectUnitCapCompilerClosedIsTrue = refl

s4RepositoryCouplingCapAtMostOneStillRequiredIsTrue :
  s4RepositoryCouplingCapAtMostOneStillRequired ≡ true
s4RepositoryCouplingCapAtMostOneStillRequiredIsTrue = refl
