{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySelectedFiniteBetaStrictPositiveExact where

------------------------------------------------------------------------
-- SELECTED LITERAL-FINITE-MODE STRICT POSITIVITY, NOT JUST HALF-FLOOR.
--
-- Explicit numerical acceptance criterion:
--
-- epsilonBudget < (11/12) * sum(per-mode lower endpoints).
--
-- This gives bLower > 0 by rational arithmetic. The existing finite-mode
-- atomwise quartic absorption then gives beta >= bLower/2 > 0, including
-- the selected CMP119 *drift-corrected* projected action difference under
-- the same source normalization as in SelectedPublishedEdgeFiniteModeFloor.
--
-- No positivity is inferred from a merely nonnegative Gaussian lower bound.
-- This is a conditional numerical criterion until real selected evaluator
-- mode lower bounds and epsilonBudget are independently certified.
--
-- Source: Bałaban CMP109 (1987), DOI: 10.1007/BF01215223.
-- DASHI: finite interval aggregation, quartic absorption and edge transport.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; Positive; _+_; _-_; _*_; _<_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (subst; subst₂; sym)

import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaLowerRemainderExact as Local
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as Finite
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as CMP119
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.Foundations.CMP119AntigravitySelectedSourceEq223SectorProjectionExact as Selected
import DASHI.Physics.Foundations.CMP119AntigravitySelectedWilsonProductDeterminesSignExact as Wilson
import DASHI.Physics.Foundations.CMP119AntigravitySelectedPublishedEdgeFiniteModeFloorExact as Floor

gaussianFloorStrictFromActualModeBudget :
  ∀ {Mode} (gaussian : Local.FiniteGaussianModeEnclosure Mode) →
  Local.epsilonBudget gaussian
    < Local.oneLoopSU2Factor * Local.computedEllLower gaussian →
  0ℚ < Local.computedGaussianLower gaussian
gaussianFloorStrictFromActualModeBudget gaussian budgetBelow =
  let
    eps = Local.epsilonBudget gaussian
    universal = Local.oneLoopSU2Factor * Local.computedEllLower gaussian
    shifted : eps + (- eps) < universal + (- eps)
    shifted = ℚP.+-monoʳ-< (- eps) budgetBelow
  in
  subst₂ _<_
    (Ring.solve-∀ eps)
    (Ring.solve-∀ universal eps)
    shifted

halfFloorStrictlyPositive :
  ∀ lower → 0ℚ < lower → 0ℚ < Local.half * lower
halfFloorStrictlyPositive lower lowerPositive =
  let
    instance halfPositive : Positive Local.half
    halfPositive = ℚ.positive (ℚP.positive⁻¹ Local.half)
    scaled : Local.half * 0ℚ < Local.half * lower
    scaled = ℚP.*-monoˡ-<-pos Local.half lowerPositive
  in
  subst
    (λ left → left < Local.half * lower)
    (ℚP.*-zeroʳ Local.half)
    scaled

module _
  {trajectory Mode Atom}
  {betaData : Finite.FiniteModeBetaTrajectoryData trajectory Mode Atom}
  (history : History.FiniteModeInverseSquareTerminalHistoryData
    trajectory Mode Atom betaData)
  {Density Background Fluctuation : Set}
  (source : CMP119.CMP119Section2SourceNativeState
    Density Background Fluctuation
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction)
  (actionMeaning : Selected.SelectedEq223RationalActionInterpretation source)
  (productMeaning : Wilson.SelectedWilsonInverseSquareNormalization history source)
  where

  selectedFiniteBetaStrictPositive :
    ∀ k →
    Local.epsilonBudget (Finite.gaussianAt betaData k)
      < Local.oneLoopSU2Factor *
        Local.computedEllLower (Finite.gaussianAt betaData k) →
    0ℚ < Flow.beta trajectory (suc k)
  selectedFiniteBetaStrictPositive k actualModeBudget =
    ℚP.<-≤-trans
      (halfFloorStrictlyPositive
        (Local.computedGaussianLower (Finite.gaussianAt betaData k))
        (gaussianFloorStrictFromActualModeBudget
          (Finite.gaussianAt betaData k) actualModeBudget))
      (Floor.sourceBetaHasFiniteGaussianHalfFloor
        history source actionMeaning productMeaning k)

  selectedCorrectedCMP119EdgeStrictPositive :
    ∀ k →
    Local.epsilonBudget (Finite.gaussianAt betaData k)
      < Local.oneLoopSU2Factor *
        Local.computedEllLower (Finite.gaussianAt betaData k) →
    0ℚ <
      - Selected.selectedProjectedEdge source k
        + (Selected.sectorProjection source k
        - Selected.sectorProjection source (suc k))
  selectedCorrectedCMP119EdgeStrictPositive k actualModeBudget =
    ℚP.<-≤-trans
      (halfFloorStrictlyPositive
        (Local.computedGaussianLower (Finite.gaussianAt betaData k))
        (gaussianFloorStrictFromActualModeBudget
          (Finite.gaussianAt betaData k) actualModeBudget))
      (Floor.selectedPublishedActionCorrectedEdgeHasGaussianHalfFloor
        history source actionMeaning productMeaning k)
