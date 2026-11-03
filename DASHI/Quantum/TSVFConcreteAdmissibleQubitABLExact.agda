{-# OPTIONS --safe #-}
module DASHI.Quantum.TSVFConcreteAdmissibleQubitABLExact where

-- The BIG quantitative finite source-to-source cut:
-- ACTUAL original BidirectionallyAdmissibleHistoryFibreExact
--   + ACTUAL original DASHI.Quantum.TSVF QuantumSurface/ABL
--   + constructive projective two-level rational amplitude coordinates
--   + original selected N-n tensor overlap from
--       TSVFAdmissibleQuantumOverlapRobustnessExact.
--
-- Both histories are permitted by ONE chosen initial/final boundary pair.
-- The Q.TSVF transition amplitudes from explicit RIGHT/WRONG projectors
-- are 5^k and 3^k; their exact Born squares are 25^k and 9^k.
-- The true original Q.TSVF.ablProbability returns the normalized fractions.
-- All statements quantify over every natural surviving environment size k.
--
-- The original TSVF abstract divideWeight interface permits a total
-- operation even on inadmissible denominators. This model represents that
-- operation as a raw fraction; for the chosen selected ensemble we prove
-- nonzero/positive denominator BEFORE invoking its ABLContext. Invalid
-- general fractions are not accepted as physical probabilities.
--
-- This is a REAL nontrivial finite amplitude/ABL calculation, not a
-- THERMODYNAMIC or PHYSICAL COMPLEX HILBERT continuum, no proof of the
-- 2017 gamma_i environment disturbances or full OS (3,1) time welding.
-- Integer nonnegative amplitude coordinates embed in the rational/real
-- 2D Hilbert inner-product sector, but are NOT a complete complex
-- Hilbert theory. This does not add a fifth time or a multiverse.
--
-- Original authors: Aharonov/Bergmann/Lebowitz; Aharonov/Vaidman;
-- Aharonov/Cohen/Gruss/Landsberger (2014); Aharonov/Cohen/Landsberger (2017).
-- Preserve original DASHI owners and Golden --safe with no local postulates.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as ℕₚ
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)

import DASHI.Quantum.TSVF as Q
import DASHI.Physics.Foundations.BidirectionallyAdmissibleHistoryFibreExact as Bidi
import DASHI.Physics.Foundations.TSVFAdmissibleQuantumOverlapRobustnessExact as Overlap

data TwoOutcome : Set where
  selectedRight : TwoOutcome
  selectedWrong : TwoOutcome

-- Actual coordinate projections, not string/Bool projector labels.
rightProjector wrongProjector : Overlap.QubitNumerator → Overlap.QubitNumerator
rightProjector (Overlap.ket₂ a b) = Overlap.ket₂ a zero
wrongProjector (Overlap.ket₂ a b) = Overlap.ket₂ zero b

selectedProjector : TwoOutcome → Overlap.QubitNumerator → Overlap.QubitNumerator
selectedProjector selectedRight = rightProjector
selectedProjector selectedWrong = wrongProjector

-- Genuine idempotent projectors on the integer-coordinate 2D carrier.
rightProjectorIdempotent :
  (v : Overlap.QubitNumerator) →
  rightProjector (rightProjector v) ≡ rightProjector v
rightProjectorIdempotent (Overlap.ket₂ a b) = refl

wrongProjectorIdempotent :
  (v : Overlap.QubitNumerator) →
  wrongProjector (wrongProjector v) ≡ wrongProjector v
wrongProjectorIdempotent (Overlap.ket₂ a b) = refl

record RationalCount : Set where
  constructor rationalCount
  field
    numerator denominator : Nat

open RationalCount public

square : Nat → Nat
square x = x * x

-- A concrete original Q.QuantumSurface, with actual two-coordinate
-- amplitudes and valid selected total. The total divideWeight API is
-- not a full field algebra on arbitrary raw zero-denominator fractions.
finiteQubitQuantum : Q.QuantumSurface
finiteQubitQuantum = record
  { Scalar = Nat
  ; Weight = RationalCount
  ; Ket = Overlap.QubitNumerator
  ; Bra = Overlap.QubitNumerator
  ; Operator = Overlap.QubitNumerator → Overlap.QubitNumerator
  ; Time = ⊤
  ; evolveKet = λ _ _ ket → ket
  ; evolveBra = λ _ _ bra → bra
  ; apply = λ projector ket → projector ket
  ; pair = Overlap.dot₂
  ; normSquared = λ amplitude → rationalCount (square amplitude) 1
  ; divideWeight = λ top bottom →
      rationalCount
        (numerator top * denominator bottom)
        (denominator top * numerator bottom)
  ; Positive = λ weight → 1 ≤ numerator weight
  }

-- This concrete choice can be viewed as k environmental tensor factors
-- condensed to their exact product amplitudes, after comparing the
-- selected pointer with the alternative in the same real 2D basis.
finiteEnsemble : Nat → Q.TSVFEnsemble finiteQubitQuantum
finiteEnsemble k =
  Q.prePostSelected
    tt tt tt
    (Overlap.ket₂ 1 1)
    (Overlap.ket₂ (Overlap.power 5 k) (Overlap.power 3 k))

rightTransitionAmplitude :
  (k : Nat) →
  Q.transitionAmplitude (finiteEnsemble k) rightProjector
  ≡ Overlap.power 5 k
rightTransitionAmplitude k
  rewrite ℕₚ.*-identityʳ (Overlap.power 5 k)
        | ℕₚ.*-zeroʳ (Overlap.power 3 k)
        | ℕₚ.+-identityʳ (Overlap.power 5 k) =
  refl

wrongTransitionAmplitude :
  (k : Nat) →
  Q.transitionAmplitude (finiteEnsemble k) wrongProjector
  ≡ Overlap.power 3 k
wrongTransitionAmplitude k
  rewrite ℕₚ.*-zeroʳ (Overlap.power 5 k)
        | ℕₚ.*-identityʳ (Overlap.power 3 k) =
  refl

rightBornNumerator :
  (k : Nat) →
  numerator (Q.transitionWeight (finiteEnsemble k) rightProjector)
  ≡ Overlap.rightRaw k
rightBornNumerator k =
  trans
    (cong square (rightTransitionAmplitude k))
    (Overlap.tensorPowerMultiplicative 5 5 k)

wrongBornNumerator :
  (k : Nat) →
  numerator (Q.transitionWeight (finiteEnsemble k) wrongProjector)
  ≡ Overlap.wrongRaw k
wrongBornNumerator k =
  trans
    (cong square (wrongTransitionAmplitude k))
    (Overlap.tensorPowerMultiplicative 3 3 k)

-- The actual original two-outcome ProjectiveMeasurement. Its denominator
-- is the sum of the two selected transition-weight numerators.
finiteProjectiveMeasurement : Q.ProjectiveMeasurement finiteQubitQuantum
finiteProjectiveMeasurement = record
  { Outcome = TwoOutcome
  ; projector = selectedProjector
  ; totalPathWeight = λ E →
      rationalCount
        (square (Q.transitionAmplitude E rightProjector)
          + square (Q.transitionAmplitude E wrongProjector))
        1
  }

finiteMeasurementDenominator :
  (k : Nat) →
  numerator
    (Q.ProjectiveMeasurement.totalPathWeight
      finiteProjectiveMeasurement (finiteEnsemble k))
  ≡ Overlap.rightRaw k + Overlap.wrongRaw k
finiteMeasurementDenominator k =
  cong₂ _+_ (rightBornNumerator k) (wrongBornNumerator k)

oneAtMostFive : 1 ≤ 5
oneAtMostFive = ℕₚ.m≤m+n 1 4

oneAtMostFivePower :
  (k : Nat) → 1 ≤ Overlap.power 5 k
oneAtMostFivePower zero = ℕₚ.≤-refl
oneAtMostFivePower (suc k) =
  ℕₚ.*-mono-≤ oneAtMostFive (oneAtMostFivePower k)

finiteMeasurementTotalPositive :
  (k : Nat) →
  1 ≤ numerator
    (Q.ProjectiveMeasurement.totalPathWeight
      finiteProjectiveMeasurement (finiteEnsemble k))
finiteMeasurementTotalPositive k
  rewrite finiteMeasurementDenominator k =
  ℕₚ.≤-trans (Overlap.oneAtMostRightPower k)
    (ℕₚ.m≤m+n (Overlap.rightRaw k) (Overlap.wrongRaw k))

-- THIS IS AN ACTUAL INHABITED original Q.ABLContext.
finiteOriginalABLContext :
  (k : Nat) →
  Q.ABLContext finiteQubitQuantum
    finiteProjectiveMeasurement (finiteEnsemble k)
finiteOriginalABLContext k =
  Q.ablContext (finiteMeasurementTotalPositive k)

-- Exact ABL fractions, from the original Q.ablProbability implementation,
-- now have the correct right/wrong selected numerators and one denominator.
finiteABLRight :
  (k : Nat) → RationalCount
finiteABLRight k =
  Q.ablProbability (finiteOriginalABLContext k) selectedRight

finiteABLWrong :
  (k : Nat) → RationalCount
finiteABLWrong k =
  Q.ablProbability (finiteOriginalABLContext k) selectedWrong

rightOriginalABLNumerator :
  (k : Nat) →
  numerator (finiteABLRight k) ≡ Overlap.rightRaw k
rightOriginalABLNumerator k =
  trans
    (cong (λ x → x * 1) (rightBornNumerator k))
    (ℕₚ.*-identityʳ (Overlap.rightRaw k))

wrongOriginalABLNumerator :
  (k : Nat) →
  numerator (finiteABLWrong k) ≡ Overlap.wrongRaw k
wrongOriginalABLNumerator k =
  trans
    (cong (λ x → x * 1) (wrongBornNumerator k))
    (ℕₚ.*-identityʳ (Overlap.wrongRaw k))

rightOriginalABLDenominator :
  (k : Nat) →
  denominator (finiteABLRight k)
  ≡ Overlap.rightRaw k + Overlap.wrongRaw k
rightOriginalABLDenominator = finiteMeasurementDenominator

wrongOriginalABLDenominator :
  (k : Nat) →
  denominator (finiteABLWrong k)
  ≡ Overlap.rightRaw k + Overlap.wrongRaw k
wrongOriginalABLDenominator = finiteMeasurementDenominator

-- We prove exact normalization for the fractions returned by the
-- ORIGINAL TSVF.ablProbability, not for a newly invented probability.
finiteOriginalABLNormalization :
  (k : Nat) →
  numerator (finiteABLRight k) + numerator (finiteABLWrong k)
  ≡ denominator (finiteABLRight k)
finiteOriginalABLNormalization k =
  trans
    (cong₂ _+_ (rightOriginalABLNumerator k)
      (wrongOriginalABLNumerator k))
    (symmetryToRightDenominator k)
  where
    symmetryToRightDenominator :
      (n : Nat) →
      Overlap.rightRaw n + Overlap.wrongRaw n
      ≡ denominator (finiteABLRight n)
    symmetryToRightDenominator n =
      sym (rightOriginalABLDenominator n)

-- Both boundary constraints genuinely admit BOTH measured histories in
-- this finite selected two-branch source. The original Bidi fibre owner
-- is instantiated, rather than being replaced by a new admissibility idea.
jointAdmissibleHistoryFibre :
  Bidi.BidirectionallyAdmissibleHistoryFibre
jointAdmissibleHistoryFibre = record
  { InitialBoundary = ⊤
  ; FinalBoundary = ⊤
  ; History = TwoOutcome
  ; admissibleFromBoth = λ _ _ _ → ⊤
  ; fibreReading =
      "Both branches satisfy both boundaries. Born amplitudes, not admissibility alone, determine their relative probabilities."
  }

selectedJointTSVFSource :
  (k : Nat) →
  Overlap.AdmissibleTSVFQuantumSource
    jointAdmissibleHistoryFibre finiteQubitQuantum (finiteEnsemble k)
selectedJointTSVFSource k = record
  { initial = tt
  ; final = tt
  ; rightHistory = selectedRight
  ; wrongHistory = selectedWrong
  ; rightAllowed = tt
  ; wrongAllowed = tt
  ; projectorOf = λ h _ → selectedProjector h
  }

-- This verifies actual SAME-projector SAME-ensemble source transport.
admissibleRightIsOriginalABLProjector :
  (k : Nat) →
  Overlap.projectorOf (selectedJointTSVFSource k)
    (Overlap.rightHistory (selectedJointTSVFSource k))
    (Overlap.rightAllowed (selectedJointTSVFSource k))
  ≡ Q.ProjectiveMeasurement.projector finiteProjectiveMeasurement selectedRight
admissibleRightIsOriginalABLProjector k = refl

admissibleWrongIsOriginalABLProjector :
  (k : Nat) →
  Overlap.projectorOf (selectedJointTSVFSource k)
    (Overlap.wrongHistory (selectedJointTSVFSource k))
    (Overlap.wrongAllowed (selectedJointTSVFSource k))
  ≡ Q.ProjectiveMeasurement.projector finiteProjectiveMeasurement selectedWrong
admissibleWrongIsOriginalABLProjector k = refl

-- EXACT SAME-OBJECT COMMUTING CROSS: the selected ABL Born masses
-- and the independently computed *tensor environment* norm/overlap
-- are related by one rational squared-overlap equality. This is not a
-- parameter "matchedWeight" that assumes the desired result.
selectedABLMatchesActualTensorOverlap :
  (k : Nat) →
  numerator (finiteABLWrong k)
    * (Overlap.tensorDot
        (Overlap.replicate Overlap.epsRight k)
        (Overlap.replicate Overlap.epsRight k)
      * Overlap.tensorDot
        (Overlap.replicate Overlap.epsWrong k)
        (Overlap.replicate Overlap.epsWrong k))
  ≡
  numerator (finiteABLRight k)
    * (Overlap.tensorDot
        (Overlap.replicate Overlap.epsRight k)
        (Overlap.replicate Overlap.epsWrong k)
      * Overlap.tensorDot
        (Overlap.replicate Overlap.epsRight k)
        (Overlap.replicate Overlap.epsWrong k))
selectedABLMatchesActualTensorOverlap k
  rewrite wrongOriginalABLNumerator k
        | rightOriginalABLNumerator k =
  trans
    (sym (Overlap.actualTensorSquaredOverlapIsNineOverTwentyFivePower k))
    (ℕₚ.*-comm
      (Overlap.tensorDot
        (Overlap.replicate Overlap.epsRight k)
        (Overlap.replicate Overlap.epsWrong k)
       * Overlap.tensorDot
        (Overlap.replicate Overlap.epsRight k)
        (Overlap.replicate Overlap.epsWrong k))
      (Overlap.rightRaw k))

-- The actual same selected two-boundary ABL model has right/left odds
-- 25^k : 9^k from k independent surviving environment factors.
-- It never asserts that every jointly admissible history has nonzero
-- amplitude or that this is a universal physical final boundary.
selectedFiniteABLRightAtLeastWrong :
  (k : Nat) →
  numerator (finiteABLWrong k) ≤ numerator (finiteABLRight k)
selectedFiniteABLRightAtLeastWrong k
  rewrite rightOriginalABLNumerator k
        | wrongOriginalABLNumerator k =
  Overlap.wrongAtMostRight k
