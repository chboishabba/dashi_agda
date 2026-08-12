module DASHI.Physics.Closure.NSTriadKNComSingleGramReductionRound40Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Mischa Cotlar; Elias M. Stein.
-- Title: "A unified theory of Hilbert transforms and ergodic theorems".
-- Proceedings of the Symposium on Ergodic Theory, 1955.
-- DOI: no DOI assigned to the cited historical conference article.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier--Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- DASHI CONTRIBUTION
--
-- Round 35's physical Com interface asked for two independent Gram cells,
-- corresponding to T_q^* T_r and T_q T_r^*.  Round 40 proves on the physical
-- Fourier matrix entries that incompressible transport is skew-adjoint, so the
-- two diagonal round trips are the two Gram faces of one cross-channel
-- operator.  This module removes the duplicated analytic obligation.
--
-- A single-channel realization supplies:
--
--   * the two literal physical pair-product scalars;
--   * their exact equality from adjunction;
--   * one GramInterferenceCell for the first face;
--   * one half-dyadic overlap estimate.
--
-- The second Round-35 cell is definitionally chosen to be the first cell, and
-- its exact product identity is derived from `pairProductsCoincide`.  Hence one
-- physical Gram estimate constructs the full mature Round-35 two-face record
-- and both Cotlar pair decays follow.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSTriadKNComGramInterferenceRound35Exact as Gram
import DASHI.Physics.Closure.NSTriadKNComCotlarDyadicEnvelopeRound34Exact as Cotlar
import DASHI.Physics.Closure.NSTriadKNLuoSixThreeComCotlarBridgeRound34Exact as Bridge

record PhysicalComSingleChannelGramRealization : Set where
  field
    firstPhysicalPairProduct : Nat → Nat → ℚ
    secondPhysicalPairProduct : Nat → Nat → ℚ
    shellDistance : Nat → Nat → Nat

    pairProductsCoincide : ∀ q r →
      firstPhysicalPairProduct q r ≡ secondPhysicalPairProduct q r

    singleGram : ∀ q r → Gram.GramInterferenceCell (shellDistance q r)

    firstProductExact : ∀ q r →
      firstPhysicalPairProduct q r
      ≡ Gram.pairProduct (singleGram q r)

    singleOverlapHalfDyadic : ∀ q r →
      Gram.overlap (singleGram q r)
      ≤ Cotlar.directEnvelope Bridge.half (shellDistance q r)

open PhysicalComSingleChannelGramRealization public

secondProductExactFromAdjointFace :
  (realization : PhysicalComSingleChannelGramRealization) →
  ∀ q r →
  secondPhysicalPairProduct realization q r
  ≡ Gram.pairProduct (singleGram realization q r)
secondProductExactFromAdjointFace realization q r =
  trans
    (sym (pairProductsCoincide realization q r))
    (firstProductExact realization q r)

fullRound35GramRealizationFromSingleChannel :
  PhysicalComSingleChannelGramRealization →
  Gram.PhysicalComPairProductGramRealization
fullRound35GramRealizationFromSingleChannel realization = record
  { leftAdjointRightProduct = firstPhysicalPairProduct realization
  ; leftRightAdjointProduct = secondPhysicalPairProduct realization
  ; shellDistance = shellDistance realization
  ; leftAdjointRightGram = singleGram realization
  ; leftRightAdjointGram = singleGram realization
  ; firstProductExact = firstProductExact realization
  ; secondProductExact = secondProductExactFromAdjointFace realization
  ; firstOverlapHalfDyadic = singleOverlapHalfDyadic realization
  ; secondOverlapHalfDyadic = singleOverlapHalfDyadic realization
  }

singleChannelFirstPairDecay :
  (realization : PhysicalComSingleChannelGramRealization) →
  ∀ q r →
  firstPhysicalPairProduct realization q r
  ≤ Cotlar.directEnvelope Bridge.half (shellDistance realization q r)
singleChannelFirstPairDecay realization =
  Gram.physicalComFirstPairDecayFromGram
    (fullRound35GramRealizationFromSingleChannel realization)

singleChannelSecondPairDecay :
  (realization : PhysicalComSingleChannelGramRealization) →
  ∀ q r →
  secondPhysicalPairProduct realization q r
  ≤ Cotlar.directEnvelope Bridge.half (shellDistance realization q r)
singleChannelSecondPairDecay realization =
  Gram.physicalComSecondPairDecayFromGram
    (fullRound35GramRealizationFromSingleChannel realization)

comSingleGramReductionClosed : Bool
comSingleGramReductionClosed = true

physicalComSingleChannelGramRealizationConstructed : Bool
physicalComSingleChannelGramRealizationConstructed = false

comSingleGramReductionClosedIsTrue :
  comSingleGramReductionClosed ≡ true
comSingleGramReductionClosedIsTrue = refl
