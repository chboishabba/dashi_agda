module DASHI.Analysis.FiniteRealQSeriesReflectionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- The supplied Aristotle development proves, for finite q-series with real
-- coefficients, the analytic reflection identity
--
--   F(-conj z) = conj(F(z)),
--
-- and uses period one to obtain mirror walls.  This module proves the exact
-- algebraic finite-series core on DASHI's existing Gaussian-integer wave
-- carrier.  It does not replace the separate continuum derivative theorem.
--
-- DASHI CONTRIBUTION
--
-- For a finite polynomial with integer coefficients evaluated on the existing
-- wave pair (re,im):
--
--   conj(eval coeffs q) = eval coeffs (conj q).
--
-- On the existing four-phase carrier this exchanges phi1 <-> phi3 and fixes
-- phi0,phi2.  At the fixed phases the entire finite q-series has zero imaginary
-- part.  Thus the reflection/fixed-wall mechanism is proved on the concrete
-- finite wave algebra already used elsewhere in DASHI.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.ShiftDiscreteWaveStep as Wave
import DASHI.Physics.ShiftPhaseTableInterference as Phase

waveExt :
  ∀ {a b c d : ℤ} →
  a ≡ c → b ≡ d →
  Wave.mkDiscreteWave a b ≡ Wave.mkDiscreteWave c d
waveExt refl refl = refl

waveZero : Wave.DiscreteWave
waveZero = Wave.mkDiscreteWave (+ 0) (+ 0)

waveReal : ℤ → Wave.DiscreteWave
waveReal value = Wave.mkDiscreteWave value (+ 0)

waveConj : Wave.DiscreteWave → Wave.DiscreteWave
waveConj value =
  Wave.mkDiscreteWave
    (Wave.DiscreteWave.re value)
    (- Wave.DiscreteWave.im value)

waveMul : Wave.DiscreteWave → Wave.DiscreteWave → Wave.DiscreteWave
waveMul left right =
  Wave.mkDiscreteWave
    (Wave.DiscreteWave.re left * Wave.DiscreteWave.re right
      - Wave.DiscreteWave.im left * Wave.DiscreteWave.im right)
    (Wave.DiscreteWave.re left * Wave.DiscreteWave.im right
      + Wave.DiscreteWave.im left * Wave.DiscreteWave.re right)

conjInvolutive :
  (value : Wave.DiscreteWave) →
  waveConj (waveConj value) ≡ value
conjInvolutive (Wave.mkDiscreteWave re im) =
  waveExt refl
    (solve 1 (λ x → :- (:- x) := x) refl im)

conjReal :
  (value : ℤ) →
  waveConj (waveReal value) ≡ waveReal value
conjReal value = refl

conjAdd :
  (left right : Wave.DiscreteWave) →
  waveConj (Wave.waveAdd left right)
  ≡ Wave.waveAdd (waveConj left) (waveConj right)
conjAdd
  (Wave.mkDiscreteWave a b)
  (Wave.mkDiscreteWave c d) =
  waveExt refl
    (solve 2
      (λ b d → :-(b :+ d) := (:- b) :+ (:- d))
      refl b d)

conjMul :
  (left right : Wave.DiscreteWave) →
  waveConj (waveMul left right)
  ≡ waveMul (waveConj left) (waveConj right)
conjMul
  (Wave.mkDiscreteWave a b)
  (Wave.mkDiscreteWave c d) =
  waveExt
    (solve 4
      (λ a b c d →
        a :* c :- b :* d
        :=
        a :* c :- ((:- b) :* (:- d)))
      refl a b c d)
    (solve 4
      (λ a b c d →
        :- (a :* d :+ b :* c)
        :=
        a :* (:- d) :+ (:- b) :* c)
      refl a b c d)

------------------------------------------------------------------------
-- Horner evaluation of a finite real-coefficient q-series.
------------------------------------------------------------------------

finiteQSeries : List ℤ → Wave.DiscreteWave → Wave.DiscreteWave
finiteQSeries [] q = waveZero
finiteQSeries (coefficient ∷ rest) q =
  Wave.waveAdd
    (waveReal coefficient)
    (waveMul q (finiteQSeries rest q))

finiteQSeriesConjugation :
  (coefficients : List ℤ) →
  (q : Wave.DiscreteWave) →
  waveConj (finiteQSeries coefficients q)
  ≡ finiteQSeries coefficients (waveConj q)
finiteQSeriesConjugation [] q = refl
finiteQSeriesConjugation (coefficient ∷ rest) q =
  trans
    (conjAdd
      (waveReal coefficient)
      (waveMul q (finiteQSeries rest q)))
    (trans
      (cong₂ Wave.waveAdd
        (conjReal coefficient)
        (conjMul q (finiteQSeries rest q)))
      (cong
        (Wave.waveAdd (waveReal coefficient))
        (cong
          (waveMul (waveConj q))
          (finiteQSeriesConjugation rest q))))

------------------------------------------------------------------------
-- Existing four-phase specialization.
------------------------------------------------------------------------

phaseConjugate : Phase.Phase4 → Phase.Phase4
phaseConjugate Phase.φ0 = Phase.φ0
phaseConjugate Phase.φ1 = Phase.φ3
phaseConjugate Phase.φ2 = Phase.φ2
phaseConjugate Phase.φ3 = Phase.φ1

phaseConjugateInvolutive :
  (phase : Phase.Phase4) →
  phaseConjugate (phaseConjugate phase) ≡ phase
phaseConjugateInvolutive Phase.φ0 = refl
phaseConjugateInvolutive Phase.φ1 = refl
phaseConjugateInvolutive Phase.φ2 = refl
phaseConjugateInvolutive Phase.φ3 = refl

conjEncodePhase :
  (phase : Phase.Phase4) →
  waveConj (Wave.encodePhase4 phase)
  ≡ Wave.encodePhase4 (phaseConjugate phase)
conjEncodePhase Phase.φ0 = refl
conjEncodePhase Phase.φ1 = refl
conjEncodePhase Phase.φ2 = refl
conjEncodePhase Phase.φ3 = refl

finiteQSeriesAtPhase :
  List ℤ → Phase.Phase4 → Wave.DiscreteWave
finiteQSeriesAtPhase coefficients phase =
  finiteQSeries coefficients (Wave.encodePhase4 phase)

finiteQSeriesPhaseReflection :
  (coefficients : List ℤ) →
  (phase : Phase.Phase4) →
  waveConj (finiteQSeriesAtPhase coefficients phase)
  ≡ finiteQSeriesAtPhase coefficients (phaseConjugate phase)
finiteQSeriesPhaseReflection coefficients phase =
  trans
    (finiteQSeriesConjugation coefficients (Wave.encodePhase4 phase))
    (cong (finiteQSeries coefficients) (conjEncodePhase phase))

------------------------------------------------------------------------
-- Fixed-phase walls: phi0 and phi2 are real q-values, and Horner evaluation
-- stays on the real axis for arbitrary integer coefficients.
------------------------------------------------------------------------

phase0SeriesImaginaryZero :
  (coefficients : List ℤ) →
  Wave.DiscreteWave.im
    (finiteQSeriesAtPhase coefficients Phase.φ0)
  ≡ + 0
phase0SeriesImaginaryZero [] = refl
phase0SeriesImaginaryZero (coefficient ∷ rest)
  rewrite phase0SeriesImaginaryZero rest = refl

phase2SeriesImaginaryZero :
  (coefficients : List ℤ) →
  Wave.DiscreteWave.im
    (finiteQSeriesAtPhase coefficients Phase.φ2)
  ≡ + 0
phase2SeriesImaginaryZero [] = refl
phase2SeriesImaginaryZero (coefficient ∷ rest)
  rewrite phase2SeriesImaginaryZero rest = refl
