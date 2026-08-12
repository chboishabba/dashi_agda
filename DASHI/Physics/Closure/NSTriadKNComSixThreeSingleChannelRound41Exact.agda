module DASHI.Physics.Closure.NSTriadKNComSixThreeSingleChannelRound41Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier--Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Mischa Cotlar; Elias M. Stein.
-- Title: "A unified theory of Hilbert transforms and ergodic theorems".
-- Proceedings of the Symposium on Ergodic Theory, 1955.
-- DOI: no DOI assigned to the cited historical conference article.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Round 35 already contains a concrete centered (L6,L3) Gram candidate whose
-- overlap satisfies the half-dyadic Cotlar envelope.  Round 40 reduced the
-- physical Com theorem from two Gram faces to one.  Therefore the shortest
-- remaining A1 same-object statement is not another abstract Gram theorem:
-- identify the literal odd P/Q pair product with the existing six-three Gram
-- pair product.
--
-- One equality
--
--   physical U_q^* U_r product
--     = pairProduct (sixThreeGramCell |q-r|)
--
-- together with the already-proved adjoint-face equality constructs the full
-- `PhysicalComSingleChannelGramRealization`, hence both mature Round-35 pair
-- decays.  The only genuinely physical producer left here is that literal
-- operator/product identification.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNComCotlarDyadicEnvelopeRound34Exact as Cotlar
import DASHI.Physics.Closure.NSTriadKNLuoSixThreeComCotlarBridgeRound34Exact as Bridge
import DASHI.Physics.Closure.NSTriadKNComGramInterferenceRound35Exact as Gram
import DASHI.Physics.Closure.NSTriadKNComSingleGramReductionRound40Exact as Single

record PhysicalComSixThreeSameObject : Set where
  field
    firstPhysicalPairProduct : Nat → Nat → ℚ
    secondPhysicalPairProduct : Nat → Nat → ℚ
    shellDistance : Nat → Nat → Nat

    pairProductsCoincide : ∀ q r →
      firstPhysicalPairProduct q r ≡ secondPhysicalPairProduct q r

    firstProductIsSixThreeGram : ∀ q r →
      firstPhysicalPairProduct q r
      ≡ Gram.pairProduct (Gram.sixThreeGramCell (shellDistance q r))

open PhysicalComSixThreeSameObject public

singleChannelGramFromSixThreeSameObject :
  PhysicalComSixThreeSameObject →
  Single.PhysicalComSingleChannelGramRealization
singleChannelGramFromSixThreeSameObject physical = record
  { firstPhysicalPairProduct = firstPhysicalPairProduct physical
  ; secondPhysicalPairProduct = secondPhysicalPairProduct physical
  ; shellDistance = shellDistance physical
  ; pairProductsCoincide = pairProductsCoincide physical
  ; singleGram = λ q r → Gram.sixThreeGramCell (shellDistance physical q r)
  ; firstProductExact = firstProductIsSixThreeGram physical
  ; singleOverlapHalfDyadic = λ q r →
      Gram.overlapHalfDyadic
        (Gram.sixThreeHalfDyadicGramCell (shellDistance physical q r))
  }

sixThreeFirstPhysicalPairDecay :
  (physical : PhysicalComSixThreeSameObject) →
  ∀ q r →
  firstPhysicalPairProduct physical q r
  ≤ Cotlar.directEnvelope Bridge.half (shellDistance physical q r)
sixThreeFirstPhysicalPairDecay physical =
  Single.singleChannelFirstPairDecay
    (singleChannelGramFromSixThreeSameObject physical)

sixThreeSecondPhysicalPairDecay :
  (physical : PhysicalComSixThreeSameObject) →
  ∀ q r →
  secondPhysicalPairProduct physical q r
  ≤ Cotlar.directEnvelope Bridge.half (shellDistance physical q r)
sixThreeSecondPhysicalPairDecay physical =
  Single.singleChannelSecondPairDecay
    (singleChannelGramFromSixThreeSameObject physical)

comSixThreeSingleChannelReductionClosed : Bool
comSixThreeSingleChannelReductionClosed = true

physicalOddPQProductEqualsSixThreeGramConstructed : Bool
physicalOddPQProductEqualsSixThreeGramConstructed = false

comSixThreeSingleChannelReductionClosedIsTrue :
  comSixThreeSingleChannelReductionClosed ≡ true
comSixThreeSingleChannelReductionClosedIsTrue = refl
