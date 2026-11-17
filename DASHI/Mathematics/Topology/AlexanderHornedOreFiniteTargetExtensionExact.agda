module DASHI.Mathematics.Topology.AlexanderHornedOreFiniteTargetExtensionExact where

------------------------------------------------------------------------
-- A CONSTRUCTIVE FINITE STAGE EXTENSION PROOF FOR THE LITERAL
-- HATCHER x -> [x_left,x_right] HORN-REFINEMENT SYSTEM.
--
-- Mathematical source:
--   Hatcher Algebraic Topology Example 2B.2 (stage maps);
--   Oystein Ore (alternating groups 1951);
--   Liebeck--O'Brien--Shalev--Tiep (Ore conjecture, JEMS 2010).
--
-- Imported source owner: AlexanderHornedC3FiniteStageExact,
-- including the SAME HornAddress, Word and expandWord.
--
-- Main result: given any target with a commutator-section
--   a = [chooseLeft(a), chooseRight(a)],
-- any proposed assignment to old meridians has an explicit
-- assignment to the new doubled meridians, with
--
-- eval(newAssignment, expandWord(w)) = eval(oldAssignment, w).
--
-- This is the actual recursive compatibility needed to extend
-- arbitrary finite alternating-group assignments in the colimit.
-- It is NOT a status bit or a source-written "proof completed" flag.
--
-- Boundary: finite A_n multiplication and Ore witnesses are not
-- constructed by this module; extending a stage-n representation
-- backwards to preceding stages and assembling the global colimit
-- hom still uses the universal property, and identifying that
-- colimit with the wild three-copy exterior requires geometry.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Mathematics.Topology.AlexanderHornedC3FiniteStageExact as H

record CommutatorSectionTarget : Set₁ where
  field
    Value : Set
    unit : Value
    multiply : Value → Value → Value
    invert : Value → Value
    associative : ∀ a b c →
      multiply (multiply a b) c ≡ multiply a (multiply b c)
    leftIdentity : ∀ a → multiply unit a ≡ a
    rightIdentity : ∀ a → multiply a unit ≡ a
    leftInverse : ∀ a → multiply (invert a) a ≡ unit
    rightInverse : ∀ a → multiply a (invert a) ≡ unit
    chooseLeft : Value → Value
    chooseRight : Value → Value
    sectionLaw : ∀ x →
      multiply
        (multiply
          (multiply (chooseLeft x) (chooseRight x))
          (invert (chooseLeft x)))
        (invert (chooseRight x))
      ≡ x

open CommutatorSectionTarget public

commutator :
  (T : CommutatorSectionTarget) →
  Value T → Value T → Value T
commutator T x y =
  multiply T
    (multiply T
      (multiply T x y)
      (invert T x))
    (invert T y)

sectionComputesCommutator :
  (T : CommutatorSectionTarget) → ∀ x →
  commutator T (chooseLeft T x) (chooseRight T x) ≡ x
sectionComputesCommutator T = sectionLaw T

Assignment : CommutatorSectionTarget → Set
Assignment T = H.HornAddress → Value T

-- The generator at old address (c,suffix) splits into children at
-- (c,left::suffix) and (c,right::suffix). The empty suffix case
-- supplies an arbitrary unused value, since new-stage generators
-- ALWAYS have at least one new bit.
nextAssignment :
  (T : CommutatorSectionTarget) →
  Assignment T → Assignment T
nextAssignment T old (H.address c []) =
  old (H.address c [])
nextAssignment T old (H.address c (H.left ∷ xs)) =
  chooseLeft T (old (H.address c xs))
nextAssignment T old (H.address c (H.right ∷ xs)) =
  chooseRight T (old (H.address c xs))

nextGeneratorImagesCommuteBack :
  (T : CommutatorSectionTarget) →
  (old : Assignment T) → ∀ a →
  commutator T
    (nextAssignment T old (H.leftChild a))
    (nextAssignment T old (H.rightChild a))
    ≡ old a
nextGeneratorImagesCommuteBack T old (H.address c xs) =
  sectionLaw T (old (H.address c xs))

evaluate :
  (T : CommutatorSectionTarget) →
  Assignment T → H.Word → Value T
evaluate T f H.unit = unit T
evaluate T f (H.generator a) = f a
evaluate T f (H.inverseWord w) = invert T (evaluate T f w)
evaluate T f (H.combine w v) =
  multiply T (evaluate T f w) (evaluate T f v)

evaluateCommutator :
  (T : CommutatorSectionTarget) →
  (f : Assignment T) → ∀ x y →
  evaluate T f (H.commutator x y)
    ≡ commutator T (evaluate T f x) (evaluate T f y)
evaluateCommutator T f x y = refl

-- Central nontrivial theorem: full word evaluation at the next
-- stage agrees with old evaluation after expanding EVERY meridian.
evaluationSurvivesOneHornRefinement :
  (T : CommutatorSectionTarget) →
  (old : Assignment T) → ∀ w →
  evaluate T (nextAssignment T old) (H.expandWord w)
    ≡ evaluate T old w
evaluationSurvivesOneHornRefinement T old H.unit = refl
evaluationSurvivesOneHornRefinement T old (H.generator a) =
  nextGeneratorImagesCommuteBack T old a
evaluationSurvivesOneHornRefinement T old (H.inverseWord w) =
  cong (invert T)
    (evaluationSurvivesOneHornRefinement T old w)
evaluationSurvivesOneHornRefinement T old (H.combine w v) =
  cong₂ (multiply T)
    (evaluationSurvivesOneHornRefinement T old w)
    (evaluationSurvivesOneHornRefinement T old v)

-- Recursively build all future assignments, reusing the exact
-- Horn address refinement rather than recreating a free group.
futureAssignments :
  (T : CommutatorSectionTarget) →
  (n : Nat) →
  Assignment T → Assignment T
futureAssignments T zero f = f
futureAssignments T (suc n) f =
  nextAssignment T (futureAssignments T n f)

evaluationSurvivesEveryFiniteRefinement :
  (T : CommutatorSectionTarget) →
  (f : Assignment T) →
  (n : Nat) → (w : H.Word) →
  evaluate T (futureAssignments T n f) (H.expandN n w)
    ≡ evaluate T f w
evaluationSurvivesEveryFiniteRefinement T f zero w = refl
evaluationSurvivesEveryFiniteRefinement T f
    (suc n) w =
  trans
    (evaluationSurvivesOneHornRefinement T
      (futureAssignments T n f) (H.expandN n w))
    (evaluationSurvivesEveryFiniteRefinement T f n w)
