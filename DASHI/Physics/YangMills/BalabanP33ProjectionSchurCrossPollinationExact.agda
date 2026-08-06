module DASHI.Physics.YangMills.BalabanP33ProjectionSchurCrossPollinationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Volker Bach, Thomas Chen, Jurg Frohlich and Israel Michael Sigal,
-- "Smooth Feshbach Map and Operator-Theoretic Renormalization Group
-- Methods", Journal of Functional Analysis 203 (2003), 44--92.
-- DOI: 10.1016/S0022-1236(03)00057-0.
--
-- Tadeusz Balaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II", Communications in Mathematical Physics 96 (1984), 223--250.
-- DOI: 10.1007/BF01240221.
--
-- DASHI CONTRIBUTION
--
-- Make the common projection-commutator interpretation concrete in the
-- Stage-II Yang--Mills lane.  The same scalar coupling b controls:
--
--   * the off-diagonal projection leakage of the retained/eliminated split;
--   * the two appearances of B in B C^-1 B^T;
--   * the one-step discounted strict-loss pullback.
--
-- This exposes a real shared invariant with the Navier--Stokes commutator
-- lane without identifying their physical operators or estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Bool using (Bool; true; false)
open import Data.Rational.Base as ℚ using
  (ℚ; _+_; _*_; _-_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst₂)

import DASHI.Physics.Common.FiniteProjectionOffDiagonalExact as Projection
import DASHI.Physics.Common.WeightedStrictLossTransportExact as Loss
import DASHI.Physics.YangMills.BalabanP33CoarseFineSchurCouplingExact as Schur
import DASHI.Physics.YangMills.BalabanP33TerminalScaleGapPullbackExact as Pullback

sharedLeakageCoefficient : ℚ → ℚ
sharedLeakageCoefficient coupling = coupling * coupling

symmetricRGBlock : ℚ → ℚ → ℚ → Projection.BlockOperator
symmetricRGBlock retainedBlock coupling fluctuationBlock =
  Projection.symmetricCouplingOperator
    retainedBlock coupling fluctuationBlock

symmetricRGProjectionLeakageExact :
  ∀ retainedBlock coupling fluctuationBlock vector →
  Projection.offDiagonalLeakageSq
    (symmetricRGBlock retainedBlock coupling fluctuationBlock)
    vector
  ≡ sharedLeakageCoefficient coupling
    * Projection.vectorNormSq vector
symmetricRGProjectionLeakageExact =
  Projection.symmetricCouplingLeakageSqExact

schurCoefficientFactorsThroughProjectionLeakage :
  ∀ coupling inverseRow inverseColumn →
  Schur.schurFeedbackSquaredCoefficient
    coupling coupling inverseRow inverseColumn
  ≡ sharedLeakageCoefficient coupling
    * (inverseRow * inverseColumn)
    * sharedLeakageCoefficient coupling
schurCoefficientFactorsThroughProjectionLeakage
    coupling inverseRow inverseColumn =
  ℚRing.solve-∀ coupling inverseRow inverseColumn

halfLossStep : ℚ → Loss.WeightedLossStep
halfLossStep loss = Loss.weightedLossStep Pullback.half loss

sharedHalfPullbackIsYMOneStep :
  ∀ coarse loss →
  Loss.pullBackFloor coarse (halfLossStep loss ∷ [])
  ≡ Pullback.half * (coarse - loss)
sharedHalfPullbackIsYMOneStep coarse loss = refl

sharedStrictMarginBelowYMOneStep :
  ∀ margin coarse loss →
  margin + Pullback.half * loss
  ≤ Pullback.half * coarse →
  margin ≤ Pullback.half * (coarse - loss)
sharedStrictMarginBelowYMOneStep margin coarse loss admissible =
  let
    steps = halfLossStep loss ∷ []

    leftTransport :
      margin + Pullback.half * loss
      ≡ margin + Loss.discountedLoss steps
    leftTransport = ℚRing.solve-∀ margin coarse loss

    rightTransport :
      Pullback.half * coarse
      ≡ Loss.terminalWeight steps * coarse
    rightTransport = ℚRing.solve-∀ margin coarse loss

    sharedBudget : Loss.StrictMarginAdmissible margin coarse steps
    sharedBudget =
      subst₂ _≤_ leftTransport rightTransport admissible
  in
  Loss.strictMarginBelowPullBack margin coarse steps sharedBudget

record YMClayCrossPollinationBoundary : Set where
  constructor ymClayCrossPollinationBoundary
  field
    projectionLeakageAndSchurShareCoupling : Bool
    projectionLeakageAndSchurShareCouplingIsTrue :
      projectionLeakageAndSchurShareCoupling ≡ true
    sharedAlgebraSuppliesPhysicalBAndCInverseBounds : Bool
    sharedAlgebraSuppliesPhysicalBAndCInverseBoundsIsFalse :
      sharedAlgebraSuppliesPhysicalBAndCInverseBounds ≡ false

canonicalYMClayCrossPollinationBoundary : YMClayCrossPollinationBoundary
canonicalYMClayCrossPollinationBoundary =
  ymClayCrossPollinationBoundary true refl false refl
