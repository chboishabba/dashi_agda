{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopSequentialContinuityRingCompilerExact where

------------------------------------------------------------------------
-- K04d-CONTINUITY: VENDORED BISHOP-REAL RING CONTINUITY.
--
-- Genuine algebraic closure for the *selected* pinned Bishop carrier.
-- No new real number type, analytic function, summation axiom,
-- setoid-to-propositional equality, or assumed continuity authority.
--
-- Inputs: the existing Sequence convergence laws, reused without
-- rebuilding epsilon-delta calculus or a classical real completion.
-- This is NOT a proof that the selected original exponential,
-- logarithm, zeta, gamma, or completed xi is continuous. It is the
-- concrete compiler those actual function continuities can consume.
--
-- Bishop/Bridges; Murray (2022); viktorcsimma/bishop pinned submodule.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Real as R
import Sequence as Seq
import RealProperties as RP

import DASHI.Analysis.BishopUniformLimitSequentialContinuityExact as U

sequentiallyContinuousConstant :
  (c : R.ℝ) →
  U.SequentiallyContinuous (λ _ → c)
sequentiallyContinuousConstant c input limit converges =
  Seq.xₙ≃c⇒xₙ→c (λ {(suc _) → RP.≃-refl})

sequentiallyContinuousIdentity :
  U.SequentiallyContinuous (λ x → x)
sequentiallyContinuousIdentity input limit converges = converges

sequentiallyContinuousAdd :
  (f g : R.ℝ → R.ℝ) →
  U.SequentiallyContinuous f →
  U.SequentiallyContinuous g →
  U.SequentiallyContinuous (λ x → R._+_ (f x) (g x))
sequentiallyContinuousAdd f g fContinuous gContinuous
    input limit converges =
  Seq.xₙ+yₙ→x₀+y₀
    (f limit , fContinuous input limit converges)
    (g limit , gContinuous input limit converges)

sequentiallyContinuousNegate :
  (f : R.ℝ → R.ℝ) →
  U.SequentiallyContinuous f →
  U.SequentiallyContinuous (λ x → R.-_ (f x))
sequentiallyContinuousNegate f fContinuous
    input limit converges =
  Seq.-xₙ→-x₀
    (f limit , fContinuous input limit converges)

sequentiallyContinuousSubtract :
  (f g : R.ℝ → R.ℝ) →
  U.SequentiallyContinuous f →
  U.SequentiallyContinuous g →
  U.SequentiallyContinuous (λ x → R._-_ (f x) (g x))
sequentiallyContinuousSubtract f g fContinuous gContinuous =
  sequentiallyContinuousAdd
    f (λ x → R.-_ (g x))
    fContinuous
    (sequentiallyContinuousNegate g gContinuous)

sequentiallyContinuousMultiply :
  (f g : R.ℝ → R.ℝ) →
  U.SequentiallyContinuous f →
  U.SequentiallyContinuous g →
  U.SequentiallyContinuous (λ x → R._*_ (f x) (g x))
sequentiallyContinuousMultiply f g fContinuous gContinuous
    input limit converges =
  Seq.xₙyₙ→x₀y₀
    (f limit , fContinuous input limit converges)
    (g limit , gContinuous input limit converges)

sequentiallyContinuousScalarMultiply :
  (c : R.ℝ) →
  (f : R.ℝ → R.ℝ) →
  U.SequentiallyContinuous f →
  U.SequentiallyContinuous (λ x → R._*_ c (f x))
sequentiallyContinuousScalarMultiply c f fContinuous =
  sequentiallyContinuousMultiply
    (λ _ → c) f
    (sequentiallyContinuousConstant c)
    fContinuous

-- Cartesian real/imaginary components of an ordinary Bishop-complex
-- multiplication. Reuse these in the original zeta/xi factor chain.
sequentiallyContinuousCartesianProductReal :
  (ar ai br bi : R.ℝ → R.ℝ) →
  U.SequentiallyContinuous ar →
  U.SequentiallyContinuous ai →
  U.SequentiallyContinuous br →
  U.SequentiallyContinuous bi →
  U.SequentiallyContinuous
    (λ x →
      R._-_
        (R._*_ (ar x) (br x))
        (R._*_ (ai x) (bi x)))
sequentiallyContinuousCartesianProductReal ar ai br bi
    arContinuous aiContinuous brContinuous biContinuous =
  sequentiallyContinuousSubtract
    (λ x → R._*_ (ar x) (br x))
    (λ x → R._*_ (ai x) (bi x))
    (sequentiallyContinuousMultiply ar br arContinuous brContinuous)
    (sequentiallyContinuousMultiply ai bi aiContinuous biContinuous)

sequentiallyContinuousCartesianProductImag :
  (ar ai br bi : R.ℝ → R.ℝ) →
  U.SequentiallyContinuous ar →
  U.SequentiallyContinuous ai →
  U.SequentiallyContinuous br →
  U.SequentiallyContinuous bi →
  U.SequentiallyContinuous
    (λ x →
      R._+_
        (R._*_ (ar x) (bi x))
        (R._*_ (ai x) (br x)))
sequentiallyContinuousCartesianProductImag ar ai br bi
    arContinuous aiContinuous brContinuous biContinuous =
  sequentiallyContinuousAdd
    (λ x → R._*_ (ar x) (bi x))
    (λ x → R._*_ (ai x) (br x))
    (sequentiallyContinuousMultiply ar bi arContinuous biContinuous)
    (sequentiallyContinuousMultiply ai br aiContinuous brContinuous)
