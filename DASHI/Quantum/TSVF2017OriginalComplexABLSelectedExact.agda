{-# OPTIONS --safe #-}
module DASHI.Quantum.TSVF2017OriginalComplexABLSelectedExact where

-- QUANTUM MAX-CUT: FINITE BUT ACTUAL COMPLEX ORIGINAL TSVF ABL.
--
-- This imports THE ORIGINAL Q.TSVF QuantumSurface, TSVFEnsemble,
-- ProjectiveMeasurement, ABLContext, ablProbability. The complex pre/post
-- kets live in a two-coordinate rational-complex inner-product space.
-- The BES is selected to be the conjugate of the intended complex
-- right/wrong branch amplitudes; a source-realistic time evolution,
-- pointer/environment unitary coupling, and a physical final cosmological
-- boundary STILL need independent real Hilbert/OS data.
--
-- The right/wrong gamma lists and k-fold environmental overlap are ACTUAL
-- complex amplitudes produced in TSVF2017ComplexEnvironmentRobustnessExact,
-- NOT free positive "Gamma_R/Gamma_W" probability constants.
--
-- Source physics: Aharonov/Bergmann/Lebowitz (1964); Aharonov/Vaidman;
-- Aharonov/Cohen/Landsberger (2017), Entropy 19:111, Eq. 22--25.
-- Reuse existing complex Cayley-Dickson and original Bidi history owner.
--
-- Completeness, orthogonality, ABL selected positivity/normalization,
-- and the environment overlap/Gamma product are mathematically separate.
-- Physical many-body (3,1) Hilbert/clock/OS and 4D Clay YM remain open.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Quantum.TSVF as Q
import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as C
import DASHI.Quantum.TSVFComplexGammaProductBornExact as Gamma
import DASHI.Quantum.TSVF2017ComplexEnvironmentRobustnessExact as Env
import DASHI.Quantum.TSVFConcreteAdmissibleQubitABLExact as OriginalBidi
import DASHI.Physics.Foundations.BidirectionallyAdmissibleHistoryFibreExact as Bidi

------------------------------------------------------------------------
-- Native two-dimensional RATIONAL-COMPLEX Hilbert inner-product carrier.
-- It is a finite pre-Hilbert sector, not completed L² of a gauge field.
------------------------------------------------------------------------

rightProjector wrongProjector :
  Env.ComplexPointerRecord → Env.ComplexPointerRecord
rightProjector (Env.pointerRecord a b) = Env.pointerRecord a C.zeroC
wrongProjector (Env.pointerRecord a b) = Env.pointerRecord C.zeroC b

rightProjectorIdempotent :
  (v : Env.ComplexPointerRecord) →
  rightProjector (rightProjector v) ≡ rightProjector v
rightProjectorIdempotent (Env.pointerRecord a b) = refl

wrongProjectorIdempotent :
  (v : Env.ComplexPointerRecord) →
  wrongProjector (wrongProjector v) ≡ wrongProjector v
wrongProjectorIdempotent (Env.pointerRecord a b) = refl

rightAfterWrongZero :
  (v : Env.ComplexPointerRecord) →
  rightProjector (wrongProjector v)
    ≡ Env.pointerRecord C.zeroC C.zeroC
rightAfterWrongZero (Env.pointerRecord a b) = refl

wrongAfterRightZero :
  (v : Env.ComplexPointerRecord) →
  wrongProjector (rightProjector v)
    ≡ Env.pointerRecord C.zeroC C.zeroC
wrongAfterRightZero (Env.pointerRecord a b) = refl

pointerAdd :
  Env.ComplexPointerRecord →
  Env.ComplexPointerRecord →
  Env.ComplexPointerRecord
pointerAdd (Env.pointerRecord a b) (Env.pointerRecord c d) =
  Env.pointerRecord (C._+c_ a c) (C._+c_ b d)

complexAddZeroRight :
  (v : C.RationalComplex) → C._+c_ v C.zeroC ≡ v
complexAddZeroRight (C.complex a b) =
  C.complexExt (solve (a ∷ [])) (solve (b ∷ []))

complexAddZeroLeft :
  (v : C.RationalComplex) → C._+c_ C.zeroC v ≡ v
complexAddZeroLeft (C.complex a b) =
  C.complexExt (solve (a ∷ [])) (solve (b ∷ []))

projectorsComplete :
  (v : Env.ComplexPointerRecord) →
  pointerAdd (rightProjector v) (wrongProjector v) ≡ v
projectorsComplete (Env.pointerRecord a b) =
  cong₂ Env.pointerRecord
    (complexAddZeroRight a)
    (complexAddZeroLeft b)

------------------------------------------------------------------------
-- Fractions are represented as rational numerator/denominator pairs.
-- The original QuantumSurface requires a total division *operation*;
-- the ABLContext prevents treating its zero-total uses as probabilities.
------------------------------------------------------------------------

record FractionWeight : Set where
  constructor fraction
  field
    numerator denominator : ℚ

open FractionWeight public

finiteComplexQuantum : Q.QuantumSurface
finiteComplexQuantum = record
  { Scalar = C.RationalComplex
  ; Weight = FractionWeight
  ; Ket = Env.ComplexPointerRecord
  ; Bra = Env.ComplexPointerRecord
  ; Operator = Env.ComplexPointerRecord → Env.ComplexPointerRecord
  ; Time = ⊤
  ; evolveKet = λ _ _ x → x
  ; evolveBra = λ _ _ x → x
  ; apply = λ op x → op x
  ; pair = Env.hermitianPair
  ; normSquared = λ amplitude → fraction (C.complexNormSq amplitude) 1ℚ
  ; divideWeight = λ top bottom →
      fraction
        (numerator top * denominator bottom)
        (denominator top * numerator bottom)
  ; Positive = λ weight →
      Σ ℚ (λ extra →
        (numerator weight ≡ 1ℚ + extra) × (0ℚ ≤ extra))
  }

-- Actual pre/post selections with gamma and tensor environment overlap.
-- The bras are conjugated because hermitianPair conjugates bra entries.
finiteComplexEnsemble :
  (rightGammas wrongGammas : List C.RationalComplex)
  (right wrong : Env.ComplexPointerRecord)
  (k : Nat) →
  Q.TSVFEnsemble finiteComplexQuantum
finiteComplexEnsemble rightGammas wrongGammas right wrong k =
  Q.prePostSelected tt tt tt
    (Env.pointerRecord C.oneC C.oneC)
    (Env.pointerRecord
      (C.conjugateC (Env.rightAmplitude rightGammas))
      (C.conjugateC
        (Env.wrongAmplitude wrongGammas right wrong k)))

finiteComplexMeasurement :
  Q.ProjectiveMeasurement finiteComplexQuantum
finiteComplexMeasurement = record
  { Outcome = OriginalBidi.TwoOutcome
  ; projector = λ
      { OriginalBidi.selectedRight → rightProjector
      ; OriginalBidi.selectedWrong → wrongProjector
      }
  ; totalPathWeight = λ ensemble →
      fraction
        (C.complexNormSq (Q.transitionAmplitude ensemble rightProjector)
          + C.complexNormSq
              (Q.transitionAmplitude ensemble wrongProjector))
        1ℚ
  }

------------------------------------------------------------------------
-- Hermitian coordinate computation: the genuine original TSVF transition
-- amplitude is exactly the corresponding complex source amplitude.
------------------------------------------------------------------------

pairRightConjugated :
  (a b : C.RationalComplex) →
  Env.hermitianPair
    (Env.pointerRecord (C.conjugateC a) (C.conjugateC b))
    (Env.pointerRecord C.oneC C.zeroC)
  ≡ a
pairRightConjugated (C.complex a b) (C.complex c d) =
  C.complexExt
    (solve (a ∷ b ∷ c ∷ d ∷ []))
    (solve (a ∷ b ∷ c ∷ d ∷ []))

pairWrongConjugated :
  (a b : C.RationalComplex) →
  Env.hermitianPair
    (Env.pointerRecord (C.conjugateC a) (C.conjugateC b))
    (Env.pointerRecord C.zeroC C.oneC)
  ≡ b
pairWrongConjugated (C.complex a b) (C.complex c d) =
  C.complexExt
    (solve (a ∷ b ∷ c ∷ d ∷ []))
    (solve (a ∷ b ∷ c ∷ d ∷ []))

rightOriginalTransitionAmplitude :
  (rightGammas wrongGammas : List C.RationalComplex)
  (right wrong : Env.ComplexPointerRecord) (k : Nat) →
  Q.transitionAmplitude
    (finiteComplexEnsemble rightGammas wrongGammas right wrong k)
    rightProjector
  ≡ Env.rightAmplitude rightGammas
rightOriginalTransitionAmplitude rightGammas wrongGammas right wrong k =
  pairRightConjugated
    (Env.rightAmplitude rightGammas)
    (Env.wrongAmplitude wrongGammas right wrong k)

wrongOriginalTransitionAmplitude :
  (rightGammas wrongGammas : List C.RationalComplex)
  (right wrong : Env.ComplexPointerRecord) (k : Nat) →
  Q.transitionAmplitude
    (finiteComplexEnsemble rightGammas wrongGammas right wrong k)
    wrongProjector
  ≡ Env.wrongAmplitude wrongGammas right wrong k
wrongOriginalTransitionAmplitude rightGammas wrongGammas right wrong k =
  pairWrongConjugated
    (Env.rightAmplitude rightGammas)
    (Env.wrongAmplitude wrongGammas right wrong k)

------------------------------------------------------------------------
-- Same *original* Q.TSVF transitionWeight and explicit source Born values.
------------------------------------------------------------------------

rightOriginalBornNumerator :
  (rightGammas wrongGammas : List C.RationalComplex)
  (right wrong : Env.ComplexPointerRecord) (k : Nat) →
  numerator
    (Q.transitionWeight
      (finiteComplexEnsemble rightGammas wrongGammas right wrong k)
      rightProjector)
  ≡ Env.rightBorn rightGammas
rightOriginalBornNumerator rightGammas wrongGammas right wrong k =
  cong C.complexNormSq
    (rightOriginalTransitionAmplitude rightGammas wrongGammas right wrong k)

wrongOriginalBornNumerator :
  (rightGammas wrongGammas : List C.RationalComplex)
  (right wrong : Env.ComplexPointerRecord) (k : Nat) →
  numerator
    (Q.transitionWeight
      (finiteComplexEnsemble rightGammas wrongGammas right wrong k)
      wrongProjector)
  ≡ Env.wrongBorn wrongGammas right wrong k
wrongOriginalBornNumerator rightGammas wrongGammas right wrong k =
  cong C.complexNormSq
    (wrongOriginalTransitionAmplitude rightGammas wrongGammas right wrong k)

originalABLTotalMatchesBornSum :
  (rightGammas wrongGammas : List C.RationalComplex)
  (right wrong : Env.ComplexPointerRecord) (k : Nat) →
  numerator
    (Q.ProjectiveMeasurement.totalPathWeight
      finiteComplexMeasurement
      (finiteComplexEnsemble rightGammas wrongGammas right wrong k))
  ≡ Env.totalBorn rightGammas wrongGammas right wrong k
originalABLTotalMatchesBornSum rightGammas wrongGammas right wrong k =
  cong₂ _+_
    (rightOriginalBornNumerator rightGammas wrongGammas right wrong k)
    (wrongOriginalBornNumerator rightGammas wrongGammas right wrong k)

------------------------------------------------------------------------
-- Actually inhabit original TSVF.ABLContext for a NONZERO selected
-- postselection: gammaRight = empty product = 1, while gammaWrong is
-- arbitrary complex and the environment states remain unrestricted.
------------------------------------------------------------------------

emptyRightGammaBornIsOne : Env.rightBorn [] ≡ 1ℚ
emptyRightGammaBornIsOne = solve []

positiveSelectedComplexABL :
  (wrongGammas : List C.RationalComplex)
  (right wrong : Env.ComplexPointerRecord) (k : Nat) →
  Q.QuantumSurface.Positive finiteComplexQuantum
    (Q.ProjectiveMeasurement.totalPathWeight
      finiteComplexMeasurement
      (finiteComplexEnsemble [] wrongGammas right wrong k))
positiveSelectedComplexABL wrongGammas right wrong k =
  Env.wrongBorn wrongGammas right wrong k
  ,
  (trans
    (originalABLTotalMatchesBornSum [] wrongGammas right wrong k)
    (cong
      (λ x → x + Env.wrongBorn wrongGammas right wrong k)
      emptyRightGammaBornIsOne)
  ,
   Env.wrongBornNonnegative wrongGammas right wrong k)

selectedOriginalABLContext :
  (wrongGammas : List C.RationalComplex)
  (right wrong : Env.ComplexPointerRecord) (k : Nat) →
  Q.ABLContext finiteComplexQuantum
    finiteComplexMeasurement
    (finiteComplexEnsemble [] wrongGammas right wrong k)
selectedOriginalABLContext wrongGammas right wrong k =
  Q.ablContext (positiveSelectedComplexABL wrongGammas right wrong k)

selectedABLRight :
  (wrongGammas : List C.RationalComplex)
  (right wrong : Env.ComplexPointerRecord) (k : Nat) → FractionWeight
selectedABLRight gammas right wrong k =
  Q.ablProbability (selectedOriginalABLContext gammas right wrong k)
    OriginalBidi.selectedRight

selectedABLWrong :
  (wrongGammas : List C.RationalComplex)
  (right wrong : Env.ComplexPointerRecord) (k : Nat) → FractionWeight
selectedABLWrong gammas right wrong k =
  Q.ablProbability (selectedOriginalABLContext gammas right wrong k)
    OriginalBidi.selectedWrong

-- The original ABL function's output numerators have the actual complex
-- Born values, even with arbitrary imaginary gamma phases.
rightABLMatchesSource :
  (gammas : List C.RationalComplex)
  (right wrong : Env.ComplexPointerRecord) (k : Nat) →
  numerator (selectedABLRight gammas right wrong k) ≡ 1ℚ
rightABLMatchesSource gammas right wrong k =
  trans
    (cong (λ x → x * 1ℚ)
      (rightOriginalBornNumerator [] gammas right wrong k))
    (trans
      (cong (λ x → x * 1ℚ) emptyRightGammaBornIsOne)
      (ℚₚ.*-identityʳ 1ℚ))

wrongABLMatchesSource :
  (gammas : List C.RationalComplex)
  (right wrong : Env.ComplexPointerRecord) (k : Nat) →
  numerator (selectedABLWrong gammas right wrong k)
  ≡ Env.wrongBorn gammas right wrong k
wrongABLMatchesSource gammas right wrong k =
  trans
    (cong (λ x → x * 1ℚ)
      (wrongOriginalBornNumerator [] gammas right wrong k))
    (ℚₚ.*-identityʳ (Env.wrongBorn gammas right wrong k))

originalABLRightDenominatorMatchesSource :
  (gammas : List C.RationalComplex)
  (right wrong : Env.ComplexPointerRecord) (k : Nat) →
  denominator (selectedABLRight gammas right wrong k)
  ≡ Env.totalBorn [] gammas right wrong k
originalABLRightDenominatorMatchesSource gammas right wrong k =
  trans
    (ℚₚ.*-identityˡ
      (numerator
        (Q.ProjectiveMeasurement.totalPathWeight
          finiteComplexMeasurement
          (finiteComplexEnsemble [] gammas right wrong k))))
    (originalABLTotalMatchesBornSum [] gammas right wrong k)

originalABLWrongDenominatorMatchesSource :
  (gammas : List C.RationalComplex)
  (right wrong : Env.ComplexPointerRecord) (k : Nat) →
  denominator (selectedABLWrong gammas right wrong k)
  ≡ Env.totalBorn [] gammas right wrong k
originalABLWrongDenominatorMatchesSource gammas right wrong k =
  trans
    (ℚₚ.*-identityˡ
      (numerator
        (Q.ProjectiveMeasurement.totalPathWeight
          finiteComplexMeasurement
          (finiteComplexEnsemble [] gammas right wrong k))))
    (originalABLTotalMatchesBornSum [] gammas right wrong k)

-- A NORMALIZATION THEOREM ON THE ORIGINAL Q.ablProbability, not on a
-- hand-written new probability function. This works with complex phases.
selectedOriginalABLNormalizes :
  (gammas : List C.RationalComplex)
  (right wrong : Env.ComplexPointerRecord) (k : Nat) →
  numerator (selectedABLRight gammas right wrong k)
    + numerator (selectedABLWrong gammas right wrong k)
  ≡ denominator (selectedABLRight gammas right wrong k)
selectedOriginalABLNormalizes gammas right wrong k =
  trans
    (cong₂ _+_
      (rightABLMatchesSource gammas right wrong k)
      (wrongABLMatchesSource gammas right wrong k))
    (trans
      (cong
        (λ x → x + Env.wrongBorn gammas right wrong k)
        (sym emptyRightGammaBornIsOne))
      (sym (originalABLRightDenominatorMatchesSource
        gammas right wrong k)))

-- An actual original-ABL mass cross identifies the same complex gamma
-- product and k-factor Hermitian environment overlap in the SAME source.
selectedOriginalABLWrongIsFactorizedGammaOverlap :
  (gammas : List C.RationalComplex)
  (right wrong : Env.ComplexPointerRecord) (k : Nat) →
  numerator (selectedABLWrong gammas right wrong k)
  ≡
  Gamma.complexGammaBornWeight gammas
    * Env.environmentBornOverlap right wrong k
selectedOriginalABLWrongIsFactorizedGammaOverlap gammas right wrong k =
  trans
    (wrongABLMatchesSource gammas right wrong k)
    (Env.wrongBornExact2017Factorization gammas right wrong k)

------------------------------------------------------------------------
-- Reuse actual original bidirectional TWO-ADMITTED/ONE-EXCLUDED history.
-- The accepted branch projectors on this COMPLEX Hilbert carrier are
-- selected from the original admissible proof, not invented by labels.
------------------------------------------------------------------------

projectorOfAdmittedHistory :
  (h : OriginalBidi.ThreeHistory) →
  Bidi.admissibleFromBoth
    OriginalBidi.jointAdmissibleHistoryFibre tt tt h →
  Env.ComplexPointerRecord → Env.ComplexPointerRecord
projectorOfAdmittedHistory
  OriginalBidi.admittedRightHistory OriginalBidi.admittedRightProof =
  rightProjector
projectorOfAdmittedHistory
  OriginalBidi.admittedWrongHistory OriginalBidi.admittedWrongProof =
  wrongProjector
projectorOfAdmittedHistory OriginalBidi.excludedHistory ()

actualComplexSelectedBidiSource :
  (gammas : List C.RationalComplex)
  (right wrong : Env.ComplexPointerRecord) (k : Nat) →
  -- The selected Q.TSVFEnsemble and joint admissible Bidi fibre agree.
  Env.ComplexPointerRecord
actualComplexSelectedBidiSource gammas right wrong k =
  Env.pointerRecord
    (Env.rightAmplitude [])
    (Env.wrongAmplitude gammas right wrong k)

-- The final mapping to the selected original Bidi record is supplied by
-- the original source's proof-carrying admittedHistoryProjector above;
-- this module does not claim a physical observer/world from that record.
