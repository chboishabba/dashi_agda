module DASHI.Physics.Closure.NSTriadKNComSingleChannelSpectralRound41Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier--Stokes Equations".
-- Communications on Pure and Applied Mathematics 41 (1988), 891--907.
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Mischa Cotlar; Elias M. Stein.
-- Title: "A unified theory of Hilbert transforms and ergodic theorems".
-- Proceedings of the Symposium on Ergodic Theory, 1955.
-- DOI: no DOI assigned to the cited historical conference article.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Round 40 proved that physical incompressible transport is skew-adjoint and
-- that the two P/Q cross channels satisfy V = -U*.  On the exact rational
-- two-channel model this implies more than equality of the two Gram faces:
-- the full commutator energy is exactly one cross-channel coefficient squared
-- times the input energy,
--
--   ||[P,T](x,y)||^2 = b^2 (x^2+y^2).
--
-- Thus the square of the commutator has precisely the same spectral size as
-- the single cross-resolution channel.  No square root or eigenvalue theorem
-- is required.  Any half-dyadic bound on b^2 immediately transports to the
-- full commutator energy.  This is the finite same-object version of
-- |[P,T]| = |U| relevant to A1/A2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNComPQCrossChannelRound37Exact as PQ
import DASHI.Physics.Closure.NSTriadKNComAdjointCollapseRound40Exact as Collapse

stateNormSquaredNonnegative :
  (state : PQ.SplitState) → 0ℚ ≤ PQ.stateNormSquared state
stateNormSquaredNonnegative state =
  L2.addNonnegative
    (L2.squareNonnegative (PQ.coarse state))
    (L2.squareNonnegative (PQ.detail state))

commutatorNormSquaredSingleChannelExact :
  ∀ {transport} →
  Collapse.SkewAdjointTransport2 transport →
  (state : PQ.SplitState) →
  PQ.stateNormSquared (PQ.commutator transport state)
  ≡
  L2.square (PQ.fineToCoarse transport)
    * PQ.stateNormSquared state
commutatorNormSquaredSingleChannelExact {transport} skew state
  rewrite PQ.commutatorNormSquaredCrossChannelExact transport state
        | Collapse.skewAdjointForcesCrossChannelsNegativeAdjoints skew =
  solve
    ( PQ.fineToCoarse transport
    ∷ PQ.coarse state
    ∷ PQ.detail state
    ∷ [])

record SingleChannelComEnergyCertificate
    (transport : PQ.LinearTransport2) : Set where
  field
    skewAdjoint : Collapse.SkewAdjointTransport2 transport
    envelope : ℚ
    envelopeNonnegative : 0ℚ ≤ envelope
    channelSquareBelowEnvelope :
      L2.square (PQ.fineToCoarse transport) ≤ envelope

open SingleChannelComEnergyCertificate public

singleChannelEnvelopeControlsFullCommutatorEnergy :
  ∀ {transport}
    (certificate : SingleChannelComEnergyCertificate transport) →
  (state : PQ.SplitState) →
  PQ.stateNormSquared (PQ.commutator transport state)
  ≤ envelope certificate * PQ.stateNormSquared state
singleChannelEnvelopeControlsFullCommutatorEnergy
    {transport} certificate state =
  let
    energyNN = stateNormSquaredNonnegative state

    scaled :
      L2.square (PQ.fineToCoarse transport)
        * PQ.stateNormSquared state
      ≤ envelope certificate * PQ.stateNormSquared state
    scaled =
      let instance energyNNI = nonNegative energyNN
      in ℚP.*-monoʳ-≤-nonNeg
        (PQ.stateNormSquared state)
        (channelSquareBelowEnvelope certificate)
  in
  subst
    (λ lower →
      lower ≤ envelope certificate * PQ.stateNormSquared state)
    (sym (commutatorNormSquaredSingleChannelExact
      (skewAdjoint certificate) state))
    scaled

singleChannelZeroForcesCommutatorZeroEnergy :
  ∀ {transport} →
  Collapse.SkewAdjointTransport2 transport →
  PQ.fineToCoarse transport ≡ 0ℚ →
  (state : PQ.SplitState) →
  PQ.stateNormSquared (PQ.commutator transport state) ≡ 0ℚ
singleChannelZeroForcesCommutatorZeroEnergy {transport} skew zeroChannel state
  rewrite commutatorNormSquaredSingleChannelExact skew state
        | zeroChannel =
  solve (PQ.stateNormSquared state ∷ [])

commutatorSquareSingleChannelReused :
  ∀ {transport} →
  Collapse.SkewAdjointTransport2 transport →
  DASHI.Physics.Closure.NSTriadKNComCrossChannelRoundTripRound39Exact.composeTransport
    (Collapse.commutatorTransport transport)
    (Collapse.commutatorTransport transport)
  ≡ PQ.linear-transport2
      (L2.square (PQ.fineToCoarse transport))
      0ℚ 0ℚ
      (L2.square (PQ.fineToCoarse transport))
commutatorSquareSingleChannelReused = Collapse.commutatorSquareSingleGram

comSingleChannelSpectralEnergyClosed : Bool
comSingleChannelSpectralEnergyClosed = true

physicalOddPQBlockSingleChannelEnvelopeConstructed : Bool
physicalOddPQBlockSingleChannelEnvelopeConstructed = false

comSingleChannelSpectralEnergyClosedIsTrue :
  comSingleChannelSpectralEnergyClosed ≡ true
comSingleChannelSpectralEnergyClosedIsTrue = refl
