module DASHI.Physics.Closure.NSTriadKNHHBadDeltaQuantifierAuditRound47Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Round 46 separated C_*(delta) from a genuinely threshold-uniform C_*.
-- Round 47 audits whether the latter can even be physically inhabited.
--
-- If the admissible threshold domain contains multiplicatively arbitrarily
-- small deltas and a fixed shell retains a positive defect floor m>0 across
-- that domain, then NO global estimate
--
--   B_q(delta) <= delta * C * 2^(-q)
--
-- can hold with one finite C.  This is the exact structural obstruction behind
-- the informal observation that a bad superlevel set may grow as delta -> 0.
--
-- The theorem is deliberately conditional on a positive floor; it does not
-- assume monotonicity or a limiting measure that the current repository has not
-- yet constructed.  It tells the physical lane exactly which quantifier must
-- fail: arbitrarily-small admissibility, positive floor, or global O(delta).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Product.Base using (_×_)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Nullary.Negation using (¬_)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp

record ThresholdDefectFamily : Set₁ where
  field
    Admissible : Threshold.PositiveThreshold → Set
    defectMass : Threshold.PositiveThreshold → Nat → ℚ
    defectMassNonnegative : ∀ parameter shell →
      0ℚ ≤ defectMass parameter shell

open ThresholdDefectFamily public

record MultiplicativelyArbitrarilySmall
    (family : ThresholdDefectFamily) : Set₁ where
  field
    smallWitness : ∀ coefficient floor →
      0ℚ < floor →
      Σ Threshold.PositiveThreshold (λ parameter →
        Admissible family parameter
        × (Threshold.threshold parameter * coefficient < floor))

open MultiplicativelyArbitrarilySmall public

record PositiveDefectFloor
    (family : ThresholdDefectFamily) : Set where
  field
    shell : Nat
    floor : ℚ
    floorPositive : 0ℚ < floor
    floorBelowEveryAdmissibleMass : ∀ parameter →
      Admissible family parameter →
      floor ≤ defectMass family parameter shell

open PositiveDefectFloor public

record GlobalLinearDeltaEnvelope
    (family : ThresholdDefectFamily) : Set where
  field
    ceiling : ℚ
    envelope : ∀ parameter shell →
      Admissible family parameter →
      defectMass family parameter shell
      ≤ Threshold.threshold parameter
        * (ceiling * Sharp.inverseDyadicScale shell)

open GlobalLinearDeltaEnvelope public

globalLinearDeltaEnvelopeNoGo :
  (family : ThresholdDefectFamily) →
  MultiplicativelyArbitrarilySmall family →
  PositiveDefectFloor family →
  ¬ GlobalLinearDeltaEnvelope family
globalLinearDeltaEnvelopeNoGo family small positiveFloor global =
  let
    coefficient =
      ceiling global * Sharp.inverseDyadicScale (shell positiveFloor)

    witness =
      smallWitness small coefficient (floor positiveFloor)
        (floorPositive positiveFloor)

    parameter = fst witness
    admissibleAndSmall = snd witness
    admissible = fst admissibleAndSmall
    smallUpper = snd admissibleAndSmall

    lowerToMass :
      floor positiveFloor
      ≤ defectMass family parameter (shell positiveFloor)
    lowerToMass =
      floorBelowEveryAdmissibleMass positiveFloor parameter admissible

    massToUpper :
      defectMass family parameter (shell positiveFloor)
      ≤ Threshold.threshold parameter * coefficient
    massToUpper =
      envelope global parameter (shell positiveFloor) admissible

    lowerToUpper :
      floor positiveFloor
      ≤ Threshold.threshold parameter * coefficient
    lowerToUpper = ℚP.≤-trans lowerToMass massToUpper

    impossible : floor positiveFloor < floor positiveFloor
    impossible = ℚP.≤-<-trans lowerToUpper smallUpper
  in
  ℚP.<-irrefl refl impossible

data DeltaUniformityRegime : Set where
  thresholdBoundedAwayFromZero : DeltaUniformityRegime
  arbitrarySmallThresholdPotentialNoGo : DeltaUniformityRegime
  intrinsicDeltaVanishingFactor : DeltaUniformityRegime

hhBadDeltaQuantifierAuditConstructed : Bool
hhBadDeltaQuantifierAuditConstructed = true

globalOdeltaCanFailForPositiveDefectFloor : Bool
globalOdeltaCanFailForPositiveDefectFloor = true

hhBadDeltaQuantifierAuditConstructedIsTrue :
  hhBadDeltaQuantifierAuditConstructed ≡ true
hhBadDeltaQuantifierAuditConstructedIsTrue = refl

globalOdeltaCanFailForPositiveDefectFloorIsTrue :
  globalOdeltaCanFailForPositiveDefectFloor ≡ true
globalOdeltaCanFailForPositiveDefectFloorIsTrue = refl
