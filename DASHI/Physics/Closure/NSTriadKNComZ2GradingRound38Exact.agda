module DASHI.Physics.Closure.NSTriadKNComZ2GradingRound38Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier--Stokes Equations".
-- Communications on Pure and Applied Mathematics 41 (1988), 891--907.
-- DOI: 10.1002/cpa.3160410704.
--
-- DASHI CONTRIBUTION
--
-- Round 37 proved [P,T] = PTQ - QTP on the exact two-channel carrier.  This
-- module exposes the equivalent Z2 grading.  With Gamma=P-Q,
--
--   Gamma^2 = I,
--   T_even = PTP + QTQ,
--   T_odd  = PTQ + QTP,
--   T = T_even + T_odd,
--   [Gamma,T] = 2 [P,T].
--
-- Hence the Com defect is entirely the oriented odd part of transport.  The
-- diagonal/even block commutes exactly and the full commutator is unchanged
-- if T is replaced by T_odd.  This is the finite algebraic reduction intended
-- to shorten the remaining physical Gram/Cotlar realization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNComPQCrossChannelRound37Exact as PQ

stateScale : ℚ → PQ.SplitState → PQ.SplitState
stateScale scalar (PQ.split-state x y) =
  PQ.split-state (scalar * x) (scalar * y)

grading : PQ.SplitState → PQ.SplitState
grading state =
  PQ.stateSubtract (PQ.projectCoarse state) (PQ.projectFine state)

gradingCoordinates : ∀ state →
  grading state ≡ PQ.split-state (PQ.coarse state) (- PQ.detail state)
gradingCoordinates (PQ.split-state x y) =
  PQ.stateExt (solve (x ∷ [])) (solve (y ∷ []))

gradingInvolution : ∀ state → grading (grading state) ≡ state
gradingInvolution (PQ.split-state x y) =
  PQ.stateExt (solve (x ∷ [])) (solve (y ∷ []))

evenTransport : PQ.LinearTransport2 → PQ.LinearTransport2
evenTransport transport =
  PQ.linear-transport2
    (PQ.coarseToCoarse transport)
    0ℚ
    0ℚ
    (PQ.fineToFine transport)

oddTransport : PQ.LinearTransport2 → PQ.LinearTransport2
oddTransport transport =
  PQ.linear-transport2
    0ℚ
    (PQ.fineToCoarse transport)
    (PQ.coarseToFine transport)
    0ℚ

transportAdd : PQ.LinearTransport2 → PQ.LinearTransport2 → PQ.LinearTransport2
transportAdd left right =
  PQ.linear-transport2
    (PQ.coarseToCoarse left + PQ.coarseToCoarse right)
    (PQ.fineToCoarse left + PQ.fineToCoarse right)
    (PQ.coarseToFine left + PQ.coarseToFine right)
    (PQ.fineToFine left + PQ.fineToFine right)

transportEvenOddDecomposition : ∀ transport →
  transportAdd (evenTransport transport) (oddTransport transport)
  ≡ transport
transportEvenOddDecomposition
    (PQ.linear-transport2 a b c d) = refl

applyEvenOddDecomposition : ∀ transport state →
  PQ.applyTransport transport state
  ≡ PQ.stateAdd
      (PQ.applyTransport (evenTransport transport) state)
      (PQ.applyTransport (oddTransport transport) state)
applyEvenOddDecomposition transport (PQ.split-state x y) =
  PQ.stateExt
    (solve
      ( PQ.coarseToCoarse transport
      ∷ PQ.fineToCoarse transport
      ∷ x ∷ y ∷ []))
    (solve
      ( PQ.coarseToFine transport
      ∷ PQ.fineToFine transport
      ∷ x ∷ y ∷ []))

gradingCommutator : PQ.LinearTransport2 → PQ.SplitState → PQ.SplitState
gradingCommutator transport state =
  PQ.stateSubtract
    (grading (PQ.applyTransport transport state))
    (PQ.applyTransport transport (grading state))

gradingCommutatorIsTwicePCommutator : ∀ transport state →
  gradingCommutator transport state
  ≡ stateScale (1ℚ + 1ℚ) (PQ.commutator transport state)
gradingCommutatorIsTwicePCommutator
    transport (PQ.split-state x y) =
  PQ.stateExt
    (solve
      ( PQ.coarseToCoarse transport
      ∷ PQ.fineToCoarse transport
      ∷ x ∷ y ∷ []))
    (solve
      ( PQ.coarseToFine transport
      ∷ PQ.fineToFine transport
      ∷ x ∷ y ∷ []))
  where open import Data.Rational.Base using (1ℚ)

evenTransportCommutesWithCoarseProjection : ∀ transport state →
  PQ.commutator (evenTransport transport) state ≡ PQ.zeroState
evenTransportCommutesWithCoarseProjection transport =
  PQ.diagonalTransportCommutesWithCoarseProjection
    (PQ.coarseToCoarse transport)
    (PQ.fineToFine transport)

oddTransportCarriesFullCommutator : ∀ transport state →
  PQ.commutator (oddTransport transport) state
  ≡ PQ.commutator transport state
oddTransportCarriesFullCommutator transport (PQ.split-state x y) =
  PQ.stateExt
    (solve
      ( PQ.coarseToCoarse transport
      ∷ PQ.fineToCoarse transport
      ∷ x ∷ y ∷ []))
    (solve
      ( PQ.coarseToFine transport
      ∷ PQ.fineToFine transport
      ∷ x ∷ y ∷ []))

oddTransportIsCrossChannelSum : ∀ transport state →
  PQ.applyTransport (oddTransport transport) state
  ≡ PQ.stateAdd
      (PQ.fineToCoarseChannel transport state)
      (PQ.coarseToFineChannel transport state)
oddTransportIsCrossChannelSum transport (PQ.split-state x y) =
  PQ.stateExt
    (solve
      (PQ.fineToCoarse transport ∷ x ∷ y ∷ []))
    (solve
      (PQ.coarseToFine transport ∷ x ∷ y ∷ []))

comZ2GradingAlgebraClosed : Bool
comZ2GradingAlgebraClosed = true

physicalOddTransportGramRealizationConstructed : Bool
physicalOddTransportGramRealizationConstructed = false

comZ2GradingAlgebraClosedIsTrue :
  comZ2GradingAlgebraClosed ≡ true
comZ2GradingAlgebraClosedIsTrue = refl
