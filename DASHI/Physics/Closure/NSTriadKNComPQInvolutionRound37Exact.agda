module DASHI.Physics.Closure.NSTriadKNComPQInvolutionRound37Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier--Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- DASHI CONTRIBUTION
--
-- Complete the P/Q/J experiment suggested by the quotient work.  On the
-- exact coarse/detail carrier define
--
--   J(x,y) = (y,x).
--
-- Then J is an involution and conjugates the complementary projections:
--
--   J^2 = I,
--   J P J = Q,
--   J Q J = P.
--
-- Conjugating a transport matrix by J swaps the two diagonal blocks and the
-- two cross channels.  This makes the coarse<->fine duality algebra explicit
-- before any shell-specific operator norm estimate is attempted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNComPQCrossChannelRound37Exact as PQ

channelInvolution : PQ.SplitState → PQ.SplitState
channelInvolution (PQ.split-state coarse detail) =
  PQ.split-state detail coarse

channelInvolutionSquared : ∀ state →
  channelInvolution (channelInvolution state) ≡ state
channelInvolutionSquared (PQ.split-state coarse detail) = refl

involutionConjugatesCoarseToFine : ∀ state →
  channelInvolution
    (PQ.projectCoarse (channelInvolution state))
  ≡ PQ.projectFine state
involutionConjugatesCoarseToFine (PQ.split-state coarse detail) = refl

involutionConjugatesFineToCoarse : ∀ state →
  channelInvolution
    (PQ.projectFine (channelInvolution state))
  ≡ PQ.projectCoarse state
involutionConjugatesFineToCoarse (PQ.split-state coarse detail) = refl

conjugateTransportByInvolution :
  PQ.LinearTransport2 → PQ.LinearTransport2
conjugateTransportByInvolution transport =
  PQ.linear-transport2
    (PQ.fineToFine transport)
    (PQ.coarseToFine transport)
    (PQ.fineToCoarse transport)
    (PQ.coarseToCoarse transport)

transportConjugationMeaning : ∀ transport state →
  PQ.applyTransport (conjugateTransportByInvolution transport) state
  ≡ channelInvolution
      (PQ.applyTransport transport (channelInvolution state))
transportConjugationMeaning transport (PQ.split-state coarse detail) =
  PQ.stateExt
    (solve
      ( PQ.fineToFine transport
      ∷ PQ.coarseToFine transport
      ∷ coarse ∷ detail ∷ []))
    (solve
      ( PQ.fineToCoarse transport
      ∷ PQ.coarseToCoarse transport
      ∷ coarse ∷ detail ∷ []))

conjugationSwapsFineToCoarseCoefficient : ∀ transport →
  PQ.fineToCoarse (conjugateTransportByInvolution transport)
  ≡ PQ.coarseToFine transport
conjugationSwapsFineToCoarseCoefficient transport = refl

conjugationSwapsCoarseToFineCoefficient : ∀ transport →
  PQ.coarseToFine (conjugateTransportByInvolution transport)
  ≡ PQ.fineToCoarse transport
conjugationSwapsCoarseToFineCoefficient transport = refl

comPQInvolutionClosed : Bool
comPQInvolutionClosed = true

comPQInvolutionClosedIsTrue : comPQInvolutionClosed ≡ true
comPQInvolutionClosedIsTrue = refl
