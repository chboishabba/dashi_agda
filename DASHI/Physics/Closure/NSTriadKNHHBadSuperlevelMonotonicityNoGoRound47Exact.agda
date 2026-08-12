module DASHI.Physics.Closure.NSTriadKNHHBadSuperlevelMonotonicityNoGoRound47Exact where

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
-- Specialize the Round-47 delta audit to the natural superlevel-set geometry.
-- If lowering delta enlarges the bad set, then the bad defect mass is
-- monotone in the reverse threshold direction:
--
--   delta_small <= delta_ref  ==>  B(delta_ref) <= B(delta_small).
--
-- Therefore ONE positive reference mass already supplies a positive floor for
-- all lower thresholds.  If admissible lower thresholds are multiplicatively
-- arbitrarily small, a global B(delta) <= delta*C*2^(-q) envelope is impossible.
--
-- This theorem exposes the precise structural danger without assuming that the
-- current physical carrier has already proved the cross-threshold nesting.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; fst; snd)
open import Data.Product.Base using (_×_)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Nullary.Negation using (¬_)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadDeltaQuantifierAuditRound47Exact as Audit

record SuperlevelThresholdMonotonicity
    (family : Audit.ThresholdDefectFamily) : Set₁ where
  field
    badMassMonotoneUnderLowerThreshold : ∀ lower higher shell →
      Audit.Admissible family lower →
      Audit.Admissible family higher →
      Threshold.threshold lower ≤ Threshold.threshold higher →
      Audit.defectMass family higher shell
      ≤ Audit.defectMass family lower shell

open SuperlevelThresholdMonotonicity public

record PositiveReferenceBadMass
    (family : Audit.ThresholdDefectFamily) : Set where
  field
    reference : Threshold.PositiveThreshold
    referenceAdmissible : Audit.Admissible family reference
    shell : Nat
    referenceMassPositive :
      0ℚ < Audit.defectMass family reference shell

open PositiveReferenceBadMass public

record ArbitrarilySmallBelowReference
    (family : Audit.ThresholdDefectFamily)
    (referenceData : PositiveReferenceBadMass family) : Set₁ where
  field
    lowerSmallWitness : ∀ coefficient →
      Σ Threshold.PositiveThreshold (λ lower →
        Audit.Admissible family lower
        × (Threshold.threshold lower
            ≤ Threshold.threshold (reference referenceData))
        × (Threshold.threshold lower * coefficient
            < Audit.defectMass family
                (reference referenceData) (shell referenceData)))

open ArbitrarilySmallBelowReference public

superlevelMonotonicityGlobalLinearNoGo :
  (family : Audit.ThresholdDefectFamily) →
  (monotone : SuperlevelThresholdMonotonicity family) →
  (referenceData : PositiveReferenceBadMass family) →
  ArbitrarilySmallBelowReference family referenceData →
  ¬ Audit.GlobalLinearDeltaEnvelope family
superlevelMonotonicityGlobalLinearNoGo
    family monotone referenceData small global =
  let
    q = shell referenceData
    referenceParameter = reference referenceData
    coefficient = Audit.ceiling global * Sharp.inverseDyadicScale q
    witness = lowerSmallWitness small coefficient
    lower = fst witness
    payload = snd witness
    lowerAdmissible = fst payload
    lowerAndSmall = snd payload
    lowerBelowReference = fst lowerAndSmall
    upperBelowReferenceMass = snd lowerAndSmall

    referenceToLowerMass :
      Audit.defectMass family referenceParameter q
      ≤ Audit.defectMass family lower q
    referenceToLowerMass =
      badMassMonotoneUnderLowerThreshold monotone
        lower referenceParameter q
        lowerAdmissible
        (referenceAdmissible referenceData)
        lowerBelowReference

    lowerMassToLinearUpper :
      Audit.defectMass family lower q
      ≤ Threshold.threshold lower * coefficient
    lowerMassToLinearUpper =
      Audit.envelope global lower q lowerAdmissible

    referenceToLinearUpper :
      Audit.defectMass family referenceParameter q
      ≤ Threshold.threshold lower * coefficient
    referenceToLinearUpper =
      ℚP.≤-trans referenceToLowerMass lowerMassToLinearUpper

    impossible :
      Audit.defectMass family referenceParameter q
      < Audit.defectMass family referenceParameter q
    impossible =
      ℚP.≤-<-trans referenceToLinearUpper upperBelowReferenceMass
  in
  ℚP.<-irrefl refl impossible

superlevelMonotonicityTurnsOnePositiveMassIntoNoGo : Bool
superlevelMonotonicityTurnsOnePositiveMassIntoNoGo = true

physicalCrossThresholdSuperlevelNestingConstructed : Bool
physicalCrossThresholdSuperlevelNestingConstructed = false

superlevelMonotonicityTurnsOnePositiveMassIntoNoGoIsTrue :
  superlevelMonotonicityTurnsOnePositiveMassIntoNoGo ≡ true
superlevelMonotonicityTurnsOnePositiveMassIntoNoGoIsTrue = refl
