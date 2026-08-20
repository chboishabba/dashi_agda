module DASHI.Physics.Closure.NSTriadKNPressureStretchingCompetitionRound78Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in generation of intense velocity gradients in
-- turbulent flows".
-- arXiv: 2308.03902.
-- DOI: 10.48550/arXiv.2308.03902.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for the
-- Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Zoran Grujic.
-- Title: "Vortex stretching and anisotropic diffusion in the 3D
-- Navier-Stokes equations".
-- arXiv: 1405.3498.
-- DOI: 10.48550/arXiv.1405.3498.
--
-- ROUND78 / PRESSURE--STRETCHING COMPETITION
--
-- Along a Lagrangian trajectory, the exact gradient equation contains
--
--   D A/Dt = -A^2 - H + nu Delta A.
--
-- For vortex stretching W=S omega, the inviscid second-growth budget contains
-- a nonnegative quadratic self-amplification W.W and a pressure-Hessian term
-- with the opposite sign.  Buaria--Pumir further separate H into local
-- isotropic and nonlocal deviatoric pieces: their DNS shows the former depletes
-- vortex stretching while the latter enables it; conditioned on intense
-- enstrophy the net pressure effect can dominate the quadratic mechanism.
--
-- This module formalizes ONLY the exact sign arithmetic needed by the B2
-- diagnostic.  Statistical/DNS statements are provenance, not theorem
-- premises.  If local depletion plus any other declared depletion dominates
-- the quadratic + nonlocal enabling side, then the net inviscid stretching
-- surplus is nonpositive.  Hence positive B2 propagation requires an actual
-- source-native surplus after the pressure/depletion side is paid.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; -_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record PressureStretchingBudget : Set where
  constructor pressure-stretching-budget
  field
    quadraticSelfAmplification : ℚ
    nonlocalDeviatoricEnable : ℚ
    localIsotropicDepletion : ℚ
    otherDepletion : ℚ

open PressureStretchingBudget public

enablingSide : PressureStretchingBudget → ℚ
enablingSide budget =
  quadraticSelfAmplification budget + nonlocalDeviatoricEnable budget

depletingSide : PressureStretchingBudget → ℚ
depletingSide budget =
  localIsotropicDepletion budget + otherDepletion budget

netStretchingSurplus : PressureStretchingBudget → ℚ
netStretchingSurplus budget = enablingSide budget - depletingSide budget

dominanceForcesNonpositiveSurplus :
  ∀ budget →
  enablingSide budget ≤ depletingSide budget →
  netStretchingSurplus budget ≤ 0ℚ
dominanceForcesNonpositiveSurplus budget enabling≤depleting =
  let
    shifted :
      enablingSide budget + (- depletingSide budget)
      ≤ depletingSide budget + (- depletingSide budget)
    shifted = ℚP.+-monoʳ-≤ (- depletingSide budget) enabling≤depleting

    rightZero :
      depletingSide budget + (- depletingSide budget) ≡ 0ℚ
    rightZero = solve (depletingSide budget ∷ [])
  in
  subst
    (λ right → netStretchingSurplus budget ≤ right)
    rightZero
    shifted

positiveSurplusRefutesDepletionDominance :
  ∀ budget →
  0ℚ < netStretchingSurplus budget →
  enablingSide budget ≤ depletingSide budget →
  0ℚ < 0ℚ
positiveSurplusRefutesDepletionDominance budget positive dominance =
  ℚP.<-≤-trans positive (dominanceForcesNonpositiveSurplus budget dominance)

record SourceNativePositiveStretchingSurplus
    (budget : PressureStretchingBudget) : Set where
  field
    quadraticNonnegative : 0ℚ ≤ quadraticSelfAmplification budget
    nonlocalEnableNonnegative : 0ℚ ≤ nonlocalDeviatoricEnable budget
    localDepletionNonnegative : 0ℚ ≤ localIsotropicDepletion budget
    otherDepletionNonnegative : 0ℚ ≤ otherDepletion budget
    strictSurplus : 0ℚ < netStretchingSurplus budget

open SourceNativePositiveStretchingSurplus public

round78PressureDepletionCanBeIgnoredInB2 : Bool
round78PressureDepletionCanBeIgnoredInB2 = false

round78PositiveB2NeedsNetCrossModeSurplusAfterDepletion : Bool
round78PositiveB2NeedsNetCrossModeSurplusAfterDepletion = true

round78PressureDepletionCanBeIgnoredInB2IsFalse :
  round78PressureDepletionCanBeIgnoredInB2 ≡ false
round78PressureDepletionCanBeIgnoredInB2IsFalse = refl

round78PositiveB2NeedsNetCrossModeSurplusAfterDepletionIsTrue :
  round78PositiveB2NeedsNetCrossModeSurplusAfterDepletion ≡ true
round78PositiveB2NeedsNetCrossModeSurplusAfterDepletionIsTrue = refl
