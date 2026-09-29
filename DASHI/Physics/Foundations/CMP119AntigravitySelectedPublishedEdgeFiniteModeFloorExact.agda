{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySelectedPublishedEdgeFiniteModeFloorExact where

------------------------------------------------------------------------
-- SAME-SOURCE QUANTITATIVE WELD
--
-- On the selected CMP119 Eq.(2.23) action (not the constructed canonical
-- action) the negative Wilson coefficient is derived from (-c_k)g_k²=1
-- using the SAME CMP109 finite-history g_k. The exact E/R/B/V projected
-- drift then gives the selected beta coefficient.
--
-- Combine that identity with the existing literal per-mode/per-atom quartic
-- absorption to prove a Gaussian HALF-FLOOR for the genuinely selected,
-- drift-CORRECTED action edge.  No new beta-positivity premise.
--
-- Outstanding: source action-algebra realization, signed Wilson product
-- law, finite literal evaluator and Gaussian same-object evidence.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (_+_; _-_; -_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as CMP119
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as Finite
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaLowerRemainderExact as Local
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.Foundations.CMP119AntigravitySelectedSourceEq223SectorProjectionExact as Selected
import DASHI.Physics.Foundations.CMP119AntigravitySelectedWilsonProductDeterminesSignExact as Wilson
import DASHI.Physics.Foundations.CMP119AntigravityPublishedEq223PhysicalBetaFromWilsonProductExact as Beta

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
  (actionMeaning :
    Selected.SelectedEq223RationalActionInterpretation source)
  (productMeaning :
    Wilson.SelectedWilsonInverseSquareNormalization history source)
  where

  sourceBetaHasFiniteGaussianHalfFloor :
    ∀ k →
    Local.half * Local.computedGaussianLower
      (Finite.gaussianAt betaData k)
    ≤ Flow.beta trajectory (suc k)
  sourceBetaHasFiniteGaussianHalfFloor k =
    let
      gaussian = Finite.gaussianAt betaData k
      interaction = Finite.interactionAt betaData k
      gaussianHalfBelowSplit :
        Local.half * Local.computedGaussianLower gaussian
        ≤ Local.betaZ gaussian + Local.betaInt interaction
      gaussianHalfBelowSplit =
        Local.betaSplitLowerAfterQuarticAbsorption
          gaussian interaction
          (Finite.gamma betaData k)
          (Finite.interactionCouplingNonnegative betaData k)
          (Finite.gammaNonnegative betaData k)
          (Finite.interactionCouplingBelowGamma betaData k)
          (Finite.interactionCoefficientTotalNonnegative betaData k)
          (Finite.quarticAbsorption betaData k)
    in
    subst
      (λ target →
        Local.half * Local.computedGaussianLower gaussian ≤ target)
      (sym (Finite.sourceBetaSplitExact betaData k))
      gaussianHalfBelowSplit

  selectedPublishedActionCorrectedEdgeHasGaussianHalfFloor :
    ∀ k →
    Local.half * Local.computedGaussianLower
      (Finite.gaussianAt betaData k)
    ≤ - Selected.selectedProjectedEdge source k
      + (Selected.sectorProjection source k
        - Selected.sectorProjection source (suc k))
  selectedPublishedActionCorrectedEdgeHasGaussianHalfFloor k =
    subst
      (λ target →
        Local.half * Local.computedGaussianLower
          (Finite.gaussianAt betaData k) ≤ target)
      (Beta.selectedPublishedActionBeta
        history source actionMeaning productMeaning k)
      (sourceBetaHasFiniteGaussianHalfFloor k)
