{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayPhysicalRGDriftToUniformInfluenceExact where

------------------------------------------------------------------------
-- R445 / R320 / R333 — a quantitative UV RG error-budget theorem.
--
-- Instead of assuming one q < 1 for every UV lattice, prove it from:
--   (i) an actual original physical-cube influence at one scale,
--  (ii) an additive bound on each ORIGINAL R445 RG refinement,
-- (iii) a uniformly summable error budget over all UV refinements.
--
-- The proof is elementary exact rational order algebra, and the
-- conclusion is a shared q0+B independent of refinement depth.
--
-- This source does NOT assert (i)-(iii) for Wilson SU(N); it explicitly
-- reduces the physical problem to the source-native RG comparisons.
-- NOT a Clay solution, not a matrix/Haar/OS theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

-- Total RG drift through the first n original refinement steps.
finiteRGDrift : (Nat → ℚ) → Nat → ℚ
finiteRGDrift increment zero = 0ℚ
finiteRGDrift increment (suc n) =
  finiteRGDrift increment n + increment n

record SelectedPhysicalRGInfluenceBudget : Set₁ where
  field
    -- Physical cube and original Gibbs action fixed by the selected
    -- Wilson/R445 same-object source (not constructed here).
    actualPhysicalCubeSide : ℚ
    actualPhysicalCubeSidePositive : 0ℚ < actualPhysicalCubeSide

    -- This is the actual original weighted block-conditional
    -- Dobrushin coefficient at each selected UV refinement depth.
    selectedPhysicalInfluence : Nat → ℚ

    referenceInfluence : ℚ
    refinementInfluenceIncrease : Nat → ℚ

    referenceInfluenceUpper :
      selectedPhysicalInfluence zero ≤ referenceInfluence

    -- Critical ORIGINAL R445 donor obligation:
    -- compare the SAME selected physical-cube Gibbs conditional at
    -- two adjacent cutoffs, NOT independent finite Haar kernels.
    eachActualRGDriftUpper :
      ∀ n →
      selectedPhysicalInfluence (suc n) ≤
      selectedPhysicalInfluence n + refinementInfluenceIncrease n

    uniformTotalRGErrorBudget : ℚ

    -- This is an infinite collection of finite, cutoff-independent
    -- inequalities. Derive from an actual geometric/polymer tail
    -- estimate; no arbitrary n-dependent bound is sufficient.
    everyFiniteRGDriftBelowBudget :
      ∀ n →
      finiteRGDrift refinementInfluenceIncrease n
      ≤ uniformTotalRGErrorBudget

    -- Can be checked once at the PHYSICAL reference scale.
    referencePlusTotalBudgetStrict :
      referenceInfluence + uniformTotalRGErrorBudget < 1ℚ

open SelectedPhysicalRGInfluenceBudget public

-- Induction on actual RG refinement depth: no dependence on total
-- lattice cutoff volume is introduced by this compiler.
selectedRGInfluenceBelowFiniteDrift :
  (source : SelectedPhysicalRGInfluenceBudget) →
  ∀ n →
  selectedPhysicalInfluence source n
  ≤ referenceInfluence source
    + finiteRGDrift (refinementInfluenceIncrease source) n
selectedRGInfluenceBelowFiniteDrift source zero =
  subst
    (λ upper → selectedPhysicalInfluence source zero ≤ upper)
    (sym (ℚP.+-identityʳ (referenceInfluence source)))
    (referenceInfluenceUpper source)
  where
    open import Relation.Binary.PropositionalEquality using (sym)
selectedRGInfluenceBelowFiniteDrift source (suc n) =
  let
    inductive = selectedRGInfluenceBelowFiniteDrift source n
    atStep =
      ℚP.≤-trans
        (eachActualRGDriftUpper source n)
        (ℚP.+-mono-≤ inductive ℚP.≤-refl)
    reassociate =
      ℚP.+-assoc
        (referenceInfluence source)
        (finiteRGDrift (refinementInfluenceIncrease source) n)
        (refinementInfluenceIncrease source n)
  in
  subst
    (λ upper → selectedPhysicalInfluence source (suc n) ≤ upper)
    reassociate atStep

-- The same strict q = q0+B works at EVERY selected UV refinement depth.
selectedRGInfluenceUniformPhysicalUpper :
  (source : SelectedPhysicalRGInfluenceBudget) →
  ∀ n →
  selectedPhysicalInfluence source n
  ≤ referenceInfluence source + uniformTotalRGErrorBudget source
selectedRGInfluenceUniformPhysicalUpper source n =
  ℚP.≤-trans
    (selectedRGInfluenceBelowFiniteDrift source n)
    (ℚP.+-mono-≤ ℚP.≤-refl
      (everyFiniteRGDriftBelowBudget source n))

-- The proof-bearing STRICT physical margin is passed unchanged;
-- clients cannot erase its dependence on the actual RG sum bound.
selectedRGInfluenceUniformStrictMargin :
  (source : SelectedPhysicalRGInfluenceBudget) →
  referenceInfluence source + uniformTotalRGErrorBudget source < 1ℚ
selectedRGInfluenceUniformStrictMargin source =
  referencePlusTotalBudgetStrict source
