module DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicHeatDampingExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Darko Mitrović.
-- Title: "A High-Frequency Tail Condition and a Diagnostic Iteration for
-- the Navier--Stokes Equations".
-- arXiv:2411.02568.
-- DOI: none assigned in the cited preprint version.
--
-- PURPOSE
-- Provide an exact rational spectral model of terminal heat damping.  One
-- resolved parabolic time unit contributes the factor 1/2.  The resulting
-- damping has the semigroup law
--
--   h(m+n)=h(m)h(n),
--
-- and a nonnegative amplitude bound transports through it.  This is the
-- dyadic algebra used by the finite far-history theorem; the analytic torus
-- kernel estimate remains a separate continuum producer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

half : ℚ
half = Int.+ 1 / 2

heatDamping : Nat → ℚ
heatDamping = Geo.pow half

powAdd :
  (ratio : ℚ) →
  (left right : Nat) →
  Geo.pow ratio (left + right)
  ≡ Geo.pow ratio left * Geo.pow ratio right
powAdd ratio zero right =
  solve (Geo.pow ratio right ∷ [])
powAdd ratio (suc left) right
  rewrite powAdd ratio left right =
  solve (ratio ∷ Geo.pow ratio left ∷ Geo.pow ratio right ∷ [])

heatSemigroup :
  (oldSteps newSteps : Nat) →
  heatDamping (oldSteps + newSteps)
  ≡ heatDamping oldSteps * heatDamping newSteps
heatSemigroup = powAdd half

dampedAmplitude : ℚ → Nat → ℚ
dampedAmplitude amplitude steps =
  amplitude * heatDamping steps

dampingTransportsAmplitudeBound :
  ∀ {amplitude energy : ℚ}
    (steps : Nat) →
  0ℚ ≤ heatDamping steps →
  amplitude ≤ energy →
  dampedAmplitude amplitude steps
  ≤ dampedAmplitude energy steps
dampingTransportsAmplitudeBound {amplitude} {energy} steps dampingNonnegative amplitudeBound =
  let
    instance
      dampingIsNonnegative = nonNegative dampingNonnegative
  in
  ℚₚ.*-monoʳ-≤-nonNeg
    (heatDamping steps)
    amplitudeBound

oldHistoryFactorisation :
  (amplitude : ℚ) →
  (terminalGap additionalAge : Nat) →
  dampedAmplitude amplitude (terminalGap + additionalAge)
  ≡ dampedAmplitude amplitude terminalGap * heatDamping additionalAge
oldHistoryFactorisation amplitude terminalGap additionalAge
  rewrite heatSemigroup terminalGap additionalAge =
  solve
    ( amplitude
    ∷ heatDamping terminalGap
    ∷ heatDamping additionalAge
    ∷ []
    )
