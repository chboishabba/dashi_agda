module DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceDynamicRarityExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Geometric-depletion references:
-- Author: Zoran Grujić.
-- Title: "A Geometric Measure-Type Regularity Criterion for Solutions to the
-- 3D Navier-Stokes Equations".
-- DOI: 10.1088/0951-7715/26/1/289.
-- arXiv DOI: 10.48550/arXiv.1111.0217.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for the
-- Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- PURPOSE
-- State and prove the exact final implication for the proposed direct F3
-- route. The comparable-shell interaction is split into good-coherence,
-- bad-coherence and residual normalized squares. If all three have one common
-- epsilon/3 tail, the total normalized interaction square tends to zero.
--
-- The module deliberately does not assert the new bad-set rarity estimate.
-- It isolates that estimate as the genuinely new geometric producer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ using (_≤_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; _/_; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoTerminalInteractionDepletionTransferExact as Limit
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNLuoFiniteHighLowDerivativeRatioExact as HL

oneThird : ℚ
oneThird = Int.+ 1 / 3

coherenceThresholdSquared : Nat → ℚ
coherenceThresholdSquared shell = Geo.pow HL.half shell

record CoherenceThreeWaySplit : Set where
  constructor coherence-three-way-split
  field
    totalNormalizedSquared : Nat → ℚ
    goodNormalizedSquared : Nat → ℚ
    badNormalizedSquared : Nat → ℚ
    residualNormalizedSquared : Nat → ℚ

    splitBound :
      (shell : Nat) →
      totalNormalizedSquared shell
      ≤ goodNormalizedSquared shell
        + badNormalizedSquared shell
        + residualNormalizedSquared shell

open CoherenceThreeWaySplit public

record CommonThreeCutoff
  (good bad residual : Nat → ℚ)
  (epsilon : ℚ) : Set where
  constructor common-three-cutoff
  field
    cutoff : Nat
    bounds :
      (shell : Nat) →
      cutoff ℕ.≤ shell →
      good shell ≤ oneThird * epsilon
      × bad shell ≤ oneThird * epsilon
      × residual shell ≤ oneThird * epsilon

open CommonThreeCutoff public

record JointThreeWayVanishing
  (good bad residual : Nat → ℚ) : Set where
  constructor joint-three-way-vanishing
  field
    commonEventuallySmall :
      (epsilon : ℚ) →
      Int.+ 0 / 1 < epsilon →
      CommonThreeCutoff good bad residual epsilon

open JointThreeWayVanishing public

threeThirdsMeaning :
  (epsilon : ℚ) →
  oneThird * epsilon + oneThird * epsilon + oneThird * epsilon
  ≡ epsilon
threeThirdsMeaning epsilon = solve (epsilon ∷ [])

coherenceSplitVanishing :
  (split : CoherenceThreeWaySplit) →
  JointThreeWayVanishing
    (goodNormalizedSquared split)
    (badNormalizedSquared split)
    (residualNormalizedSquared split) →
  Limit.TendsToZero (totalNormalizedSquared split)
coherenceSplitVanishing split joint =
  Limit.tends-to-zero
    (λ epsilon epsilonPositive →
      let
        witness = commonEventuallySmall joint epsilon epsilonPositive
      in
      Limit.eventually-below
        (cutoff witness)
        (λ shell cutoff≤shell →
          let
            componentBounds = bounds witness shell cutoff≤shell
            goodBound = proj₁ componentBounds
            badBound = proj₁ (proj₂ componentBounds)
            residualBound = proj₂ (proj₂ componentBounds)

            summed :
              goodNormalizedSquared split shell
                + badNormalizedSquared split shell
                + residualNormalizedSquared split shell
              ≤ oneThird * epsilon
                + oneThird * epsilon
                + oneThird * epsilon
            summed =
              ℚₚ.+-mono-≤
                (ℚₚ.+-mono-≤ goodBound badBound)
                residualBound
          in
          ℚₚ.≤-trans
            (splitBound split shell)
            (subst
              (λ upper →
                goodNormalizedSquared split shell
                  + badNormalizedSquared split shell
                  + residualNormalizedSquared split shell
                ≤ upper)
              (threeThirdsMeaning epsilon)
              summed)))

record BadRarityBridge : Set where
  constructor bad-rarity-bridge
  field
    badNormalizedSquared badRarity : Nat → ℚ
    badByRarity :
      (shell : Nat) →
      badNormalizedSquared shell ≤ badRarity shell

open BadRarityBridge public

badInteractionVanishingFromRarity :
  (bridge : BadRarityBridge) →
  Limit.TendsToZero (badRarity bridge) →
  Limit.TendsToZero (badNormalizedSquared bridge)
badInteractionVanishingFromRarity bridge rarityVanishing =
  Limit.interactionDepletionFromCriticalDepletion
    (Limit.critical-to-interaction-data
      (badNormalizedSquared bridge)
      (badRarity bridge)
      (badByRarity bridge))
    rarityVanishing

record GoodCoherenceBridge : Set where
  constructor good-coherence-bridge
  field
    goodNormalizedSquared goodEnvelope : Nat → ℚ
    goodByEnvelope :
      (shell : Nat) →
      goodNormalizedSquared shell ≤ goodEnvelope shell

open GoodCoherenceBridge public

goodInteractionVanishingFromCoherenceEnvelope :
  (bridge : GoodCoherenceBridge) →
  Limit.TendsToZero (goodEnvelope bridge) →
  Limit.TendsToZero (goodNormalizedSquared bridge)
goodInteractionVanishingFromCoherenceEnvelope bridge envelopeVanishing =
  Limit.interactionDepletionFromCriticalDepletion
    (Limit.critical-to-interaction-data
      (goodNormalizedSquared bridge)
      (goodEnvelope bridge)
      (goodByEnvelope bridge))
    envelopeVanishing
