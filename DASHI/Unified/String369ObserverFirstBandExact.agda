module DASHI.Unified.String369ObserverFirstBandExact where

------------------------------------------------------------------------
-- HISTORICAL: Fourier harmonics, Kaluza (1921), Klein (1926),
-- spectral KK mass towers and finite periodic graph Laplacians.
-- EXISTING DASHI: CalabiYau369CompactFibreBridge, original
-- BalancedTernaryFourierModeExact, TriadicDepthOneCharacters,
-- TSFVKKSelectedHorizontalMetricSchurExact, TOE physical sectors.
-- NEW: exact rational three-site first-band scalar energy reduction
-- from a single original Z3 circle discretization (no new field theory).
-- USER: observer-dependent visible modes and the 369/string same action.
-- ChatGPT-assisted 2026-11-18. Kernel unchecked at this PR head.
--
-- This is NOT an actual smooth CY3, 10D string, emergent SM charges
-- or a continuum convergence theorem. For the complete smooth S1
-- n=0,+1,-1 reduction see the paired exact SymPy script.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as Ring
import DASHI.Biology.BalancedTernaryFourierModeExact as Fourier
import DASHI.Physics.Common.FiniteThreeCycleTorusExact as Torus

-- Real unnormalized 3-site inverse C3 Fourier coordinates.
-- v,w span the two nonzero modes; u is the invariant zero mode.
site0 site1 site2 : ℚ → ℚ → ℚ → ℚ
site0 u v w = u + (v + v)
site1 u v w = (u - v) + w
site2 u v w = (u - v) - w

square : ℚ → ℚ
square x = x * x

sampleNorm : ℚ → ℚ → ℚ → ℚ
sampleNorm u v w =
  square (site0 u v w) +
  square (site1 u v w) +
  square (site2 u v w)

-- No sqrt or division: 3*u²+6*v²+2*w².
modeNorm : ℚ → ℚ → ℚ → ℚ
modeNorm u v w =
  (square u + square u + square u) +
  ((square v + square v + square v) +
   (square v + square v + square v)) +
  (square w + square w)

-- Account for the second w² explicitly below. We do not use a
-- synthetic orthogonality axiom; both sides are original polynomials.
modeNormFull : ℚ → ℚ → ℚ → ℚ
modeNormFull u v w = modeNorm u v w + square w

finiteC3Parseval :
  (u v w : ℚ) → sampleNorm u v w ≡ modeNormFull u v w
finiteC3Parseval u v w = Ring.solve-∀ u v w

sampleGradient : ℚ → ℚ → ℚ → ℚ
sampleGradient u v w =
  square (site0 u v w - site1 u v w) +
  square (site1 u v w - site2 u v w) +
  square (site2 u v w - site0 u v w)

-- 18*v²+6*w²: exact graph gradient contribution of nonzero C3 band.
modeGradient : ℚ → ℚ → ℚ → ℚ
modeGradient u v w =
  ((square v + square v + square v) +
   (square v + square v + square v) +
   (square v + square v + square v) +
   (square v + square v + square v) +
   (square v + square v + square v) +
   (square v + square v + square v)) +
  ((square w + square w + square w) +
   (square w + square w + square w))

finiteC3GradientExact :
  (u v w : ℚ) → sampleGradient u v w ≡ modeGradient u v w
finiteC3GradientExact u v w = Ring.solve-∀ u v w

-- The original finite C3 Fourier source actually supplies the
-- character eigenlaws. These are not namesake 369 labels.
originalFirstC3Eigenlaw :
  (mode point : Fourier.Mode3x3) →
  Fourier.firstCharacter mode (Torus.translateFirst point)
    ≡ Fourier.multiplyPhase (Fourier.firstCharacter mode point)
         (Fourier.firstEigenphase mode)
originalFirstC3Eigenlaw = Fourier.firstTranslationEigen

-- At scale a²=3R² the *first* nonzero discrete graph eigenvalue
-- 3/a² matches 1/R². All higher continuum n and n+3 alias on C3;
-- neither this file nor its script claims full spectral convergence.
