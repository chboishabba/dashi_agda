{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityPublishedEq223PhysicalBetaFromWilsonProductExact where

------------------------------------------------------------------------
-- CMP119 SOURCE-FIRST LITERAL BETA PRODUCER
--
-- The selected source's WHOLE Eq.(2.23) action supplies Pi(A_k-A_(k+1)).
-- Its four selected non-Wilson terms supply the correction.
-- Its Wilson product law (-c)g²=1 and SAME finite-history g supply
-- c=-u by positive rational cancellation, not a bare same-coefficient axiom.
--
-- Remaining PHYSICAL inputs: prove the selected source's actual action
-- algebra maps to T4, its Wilson basis is unit-normalized, and derive the
-- Wilson product law from the published action/trace convention. Those are
-- strictly narrower than assuming the theorem's beta equality.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; _+_; _-_; -_)
import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as CMP119
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.Foundations.CMP119AntigravitySelectedSourceEq223SectorProjectionExact as Selected
import DASHI.Physics.Foundations.CMP119AntigravitySelectedWilsonProductDeterminesSignExact as Wilson

module _
  {trajectory Mode Atom betaData}
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

  selectedPublishedActionBeta :
    ∀ k →
    Flow.beta trajectory (suc k)
    ≡ - Selected.selectedProjectedEdge source k
      + (Selected.sectorProjection source k
         - Selected.sectorProjection source (suc k))
  selectedPublishedActionBeta =
    Selected.selectedSourceNegativeWilsonBeta source
      actionMeaning trajectory
      (Wilson.publishedWilsonIsNegativeCMP109Inverse
        history source productMeaning)
