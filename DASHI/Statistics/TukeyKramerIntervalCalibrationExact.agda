module DASHI.Statistics.TukeyKramerIntervalCalibrationExact where

-- Exact conservative interval-evaluation companion to
-- DASHI.Statistics.TukeyKramerPostHocExact.
-- HSD is different from Tukey's existing robust IQR fence.
--
-- The studentized-range qcrit^2 is generally irrational. Rather than
-- pretend a rounded q is exact, keep qcrit^2 inside a lower/upper rational
-- bracket: reject only if statistic > UPPER; fail only if <= LOWER;
-- otherwise unresolved at the declared precision.
-- This is a finite rational DECISION KERNEL. Establishing that true
-- studentized-range qcrit lies in the bracket, and that classical normal/
-- independent/homoscedastic assumptions are physically warranted,
-- are external analytic/provenance obligations.
--
-- qcrit for alpha .05, k=3, df=27 is approximately 3.506426123354149,
-- square ~12.295024158540405. The bracket 12.295 to 12.296 is an
-- illustrative numerical enclosure, NOT an interval-certified evaluation
-- of the studentized-range distribution.

open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Statistics.TukeyKramerPostHocExact as HSD

record RangeQuantileBracket : Set where
  constructor quantile-bracket
  field
    lowerNumerator : Nat
    lowerDenominator : Nat
    upperNumerator : Nat
    upperDenominator : Nat
    sourceCertifiedInclusion : Bool
open RangeQuantileBracket public

data ConservativeDecision : Set where
  notAdmitted : ConservativeDecision
  definitelyReject : ConservativeDecision
  definitelyNotReject : ConservativeDecision
  quantilePrecisionInsufficient : ConservativeDecision

validBracket : RangeQuantileBracket → Bool
validBracket bracket =
  HSD.andBool (HSD.lt 0 (lowerDenominator bracket))
  (HSD.andBool (HSD.lt 0 (upperDenominator bracket))
  (HSD.andBool
    (HSD.leq
      (lowerNumerator bracket * upperDenominator bracket)
      (upperNumerator bracket * lowerDenominator bracket))
    (sourceCertifiedInclusion bracket)))

decideConservatively :
  HSD.PostHocDesign → RangeQuantileBracket →
  HSD.GroupSummary → HSD.GroupSummary → ConservativeDecision
decideConservatively design bracket a b
  with HSD.andBool (HSD.admitted design a b) (validBracket bracket) |
       HSD.lt
         (HSD.statisticDenominator design a b * upperNumerator bracket)
         (HSD.statisticNumerator design a b * upperDenominator bracket) |
       HSD.leq
         (HSD.statisticNumerator design a b * lowerDenominator bracket)
         (HSD.statisticDenominator design a b * lowerNumerator bracket)
... | false | _ | _ = notAdmitted
... | true | true | _ = definitelyReject
... | true | false | true = definitelyNotReject
... | true | false | false = quantilePrecisionInsufficient

-- This source flag denotes a claimed calibration receipt; no theorem in
-- this module manufactures a genuine studentized-range distribution bound.
illustrativeBracket : RangeQuantileBracket
illustrativeBracket =
  quantile-bracket 12295 1000 12296 1000 true

bracketedHighContrast :
  decideConservatively HSD.syntheticDesign illustrativeBracket
    HSD.groupMean10 HSD.groupMean16 ≡ definitelyReject
bracketedHighContrast = refl

bracketedSmallContrast :
  decideConservatively HSD.syntheticDesign illustrativeBracket
    HSD.groupMean10 HSD.groupMean11 ≡ definitelyNotReject
bracketedSmallContrast = refl

-- A borderline q^2=12.2954 is deliberately difficult to express as an
-- integer group fixture; the guard is defined for it analytically by
-- the same integer threshold comparison on its numerator/denominator.
bracketMiddleIsBetween :
  HSD.lt (12295 * 10000) (122954 * 1000) ≡ true
bracketMiddleIsBetween = refl

bracketMiddleIsBelowUpper :
  HSD.lt (122954 * 1000) (12296 * 10000) ≡ true
bracketMiddleIsBelowUpper = refl

uncertifiedIllustrativeBracket : RangeQuantileBracket
uncertifiedIllustrativeBracket =
  quantile-bracket 12295 1000 12296 1000 false

uncertifiedDoesNotAdmit :
  decideConservatively HSD.syntheticDesign uncertifiedIllustrativeBracket
    HSD.groupMean10 HSD.groupMean16 ≡ notAdmitted
uncertifiedDoesNotAdmit = refl

data FloatingPointCriticalValueIsExactCertificate : Set where
data NamedVarianceAssumptionsAreActualMeasurements : Set where

noRoundedQuantileAsProof :
  FloatingPointCriticalValueIsExactCertificate → ⊥
noRoundedQuantileAsProof ()
noAssumptionFlagsAsRawEvidence :
  NamedVarianceAssumptionsAreActualMeasurements → ⊥
noAssumptionFlagsAsRawEvidence ()
