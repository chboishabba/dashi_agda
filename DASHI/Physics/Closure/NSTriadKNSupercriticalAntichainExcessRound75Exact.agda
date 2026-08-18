module DASHI.Physics.Closure.NSTriadKNSupercriticalAntichainExcessRound75Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: P. A. P. Moran.
-- Title: "Additive functions of intervals and Hausdorff measure".
-- DOI: 10.1017/S0305004100022684.
--
-- Author: John E. Hutchinson.
-- Title: "Fractals and self-similarity".
-- DOI: 10.1512/iumj.1981.30.30055.
--
-- ROUND75 / SUPERCRITICAL ANTICHAIN EXCESS
--
-- For a Round74 supercritical row
--
--     sum_i r_i^2 = 1 + epsilon,
--
-- the child squared floor is exactly
--
--     mu^2 + mu^2 epsilon.
--
-- This module sums that identity over an arbitrary irregular antichain.  The
-- correct generation-level invariant is therefore not minimum arity and not a
-- uniform child loss; it is the ACTUAL weighted excess
--
--     Delta = sum_parent mu_parent^2 epsilon_parent.
--
-- and one generation satisfies exactly
--
--     M_child = M_parent + Delta.
--
-- This is the weakest finite arithmetic target for the physical supercritical
-- route.  No fractal dimension theorem is imported.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNDeterministicIrregularSquaredCascadeRound74Exact as Cascade
import DASHI.Physics.Closure.NSTriadKNCriticalCauchyCardinalityDilutionNoGoRound71Exact as Mass
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

superParentMass : List Cascade.SupercriticalSquaredPropagationRow → ℚ
superParentMass [] = 0ℚ
superParentMass (row ∷ rows) =
  L2.square (Cascade.superParentAmplitude row) + superParentMass rows

superChildMass : List Cascade.SupercriticalSquaredPropagationRow → ℚ
superChildMass [] = 0ℚ
superChildMass (row ∷ rows) =
  Mass.squaredMass
    (Cascade.irregularChildAmplitudes
      (Cascade.superParentAmplitude row)
      (Cascade.superChildLossWeights row))
  + superChildMass rows

weightedExcessMass : List Cascade.SupercriticalSquaredPropagationRow → ℚ
weightedExcessMass [] = 0ℚ
weightedExcessMass (row ∷ rows) =
  L2.square (Cascade.superParentAmplitude row)
    * Cascade.superExcessSquaredMass row
  + weightedExcessMass rows

supercriticalGenerationExcessExact :
  ∀ rows →
  superChildMass rows
  ≡ superParentMass rows + weightedExcessMass rows
supercriticalGenerationExcessExact [] = refl
supercriticalGenerationExcessExact (row ∷ rows) =
  trans
    (cong
      (_+ superChildMass rows)
      (Cascade.supercriticalRowExcessExact row))
    (trans
      (cong
        (λ tail →
          ( L2.square (Cascade.superParentAmplitude row)
          + L2.square (Cascade.superParentAmplitude row)
            * Cascade.superExcessSquaredMass row)
          + tail)
        (supercriticalGenerationExcessExact rows))
      (solve
        ( L2.square (Cascade.superParentAmplitude row)
        ∷ Cascade.superExcessSquaredMass row
        ∷ superParentMass rows
        ∷ weightedExcessMass rows
        ∷ [])))

record SupercriticalAntichainStep : Set where
  constructor supercritical-antichain-step
  field
    rows : List Cascade.SupercriticalSquaredPropagationRow
    parentMass : ℚ
    childMass : ℚ
    excessMass : ℚ
    parentMassExact : parentMass ≡ superParentMass rows
    childMassExact : childMass ≡ superChildMass rows
    excessMassExact : excessMass ≡ weightedExcessMass rows

open SupercriticalAntichainStep public

antichainStepExactGrowth :
  (step : SupercriticalAntichainStep) →
  childMass step ≡ parentMass step + excessMass step
antichainStepExactGrowth step =
  trans
    (childMassExact step)
    (trans
      (supercriticalGenerationExcessExact (rows step))
      (cong₂ _+_
        (sym (parentMassExact step))
        (sym (excessMassExact step))))

round75SupercriticalAntichainWeightedExcessIdentified : Bool
round75SupercriticalAntichainWeightedExcessIdentified = true

round75SupercriticalAntichainExactGrowthCompilerConstructed : Bool
round75SupercriticalAntichainExactGrowthCompilerConstructed = true

round75PhysicalNSWeightedExcessLowerBoundConstructed : Bool
round75PhysicalNSWeightedExcessLowerBoundConstructed = false

round75SupercriticalAntichainExactGrowthCompilerConstructedIsTrue :
  round75SupercriticalAntichainExactGrowthCompilerConstructed ≡ true
round75SupercriticalAntichainExactGrowthCompilerConstructedIsTrue = refl
