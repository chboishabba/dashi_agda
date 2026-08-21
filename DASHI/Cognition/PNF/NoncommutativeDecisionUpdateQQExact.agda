module DASHI.Cognition.PNF.NoncommutativeDecisionUpdateQQExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Literature calibration:
--
-- Jennifer S. Trueblood; Jerome R. Busemeyer,
-- "A Quantum Probability Account of Order Effects in Inference",
-- DOI 10.1111/j.1551-6709.2011.01197.x.
--
-- James M. Yearsley; Jerome R. Busemeyer,
-- "Quantum cognition and decision theories: A tutorial",
-- DOI 10.1016/j.jmp.2015.11.005.
--
-- Masanao Ozawa; Andrei Khrennikov,
-- "Modeling combination of question order effect, response replicability
-- effect, and QQ-equality with quantum instruments",
-- DOI 10.1016/j.jmp.2020.102491.
--
-- Andrei Khrennikov; Masanao Ozawa; Felix Benninger; Oded Shor,
-- "Coupling quantum-like cognition with the neuronal networks within
-- generalized probability theory", DOI 10.1016/j.jmp.2025.102923.
--
-- The exact finite statements below use the literature distinction between
-- observable order statistics and state-update structure.  They do not claim
-- physical quantum dynamics in the brain, and QQ equality is kept as a
-- model-class diagnostic rather than a universal human-decision law.
------------------------------------------------------------------------

record BeliefState : Set where
  constructor belief
  field
    answerA : Bool
    answerB : Bool
    trace : Bool

open BeliefState public

initial : BeliefState
initial = belief false false false

observeA : BeliefState → Bool
observeA = answerA

observeB : BeliefState → Bool
observeB = answerB

observeAThenB : BeliefState → Bool × Bool
observeAThenB s = observeA s , observeB s

observeBThenA : BeliefState → Bool × Bool
observeBThenA s = observeA s , observeB s

staticObservablesCommute : (s : BeliefState) →
  observeAThenB s ≡ observeBThenA s
staticObservablesCommute s = refl

updateA : BeliefState → BeliefState
updateA (belief _ b _) = belief true b false

updateB : BeliefState → BeliefState
updateB (belief a _ _) = belief a true a

AB : BeliefState
AB = updateB (updateA initial)

BA : BeliefState
BA = updateA (updateB initial)

updateMapsDoNotCommute : AB ≡ BA → ⊥
updateMapsDoNotCommute ()

observableCommutationDoesNotForceUpdateCommutation :
  observeAThenB initial ≡ observeBThenA initial
  × (AB ≡ BA → ⊥)
observableCommutationDoesNotForceUpdateCommutation = refl , updateMapsDoNotCommute

record QQCounts : Set where
  constructor qqCounts
  field
    ByAy BnAn AyBy AnBn : Nat
    AyBn AnBy ByAn BnAy : Nat

open QQCounts public

qqFirstLeft : QQCounts → Nat
qqFirstLeft q = ByAy q + BnAn q

qqFirstRight : QQCounts → Nat
qqFirstRight q = AyBy q + AnBn q

qqSecondLeft : QQCounts → Nat
qqSecondLeft q = AyBn q + AnBy q

qqSecondRight : QQCounts → Nat
qqSecondRight q = ByAn q + BnAy q

record QQSatisfied (q : QQCounts) : Set where
  constructor qqSatisfied
  field
    firstBalance : qqFirstLeft q ≡ qqFirstRight q
    secondBalance : qqSecondLeft q ≡ qqSecondRight q

projectiveLikeCounts : QQCounts
projectiveLikeCounts = qqCounts 2 3 1 4 4 1 2 3

projectiveLikeSatisfiesQQ : QQSatisfied projectiveLikeCounts
projectiveLikeSatisfiesQQ = qqSatisfied refl refl

violatingCounts : QQCounts
violatingCounts = qqCounts 2 3 1 3 4 1 2 3

violatingCountsFailFirstBalance :
  qqFirstLeft violatingCounts ≡ qqFirstRight violatingCounts → ⊥
violatingCountsFailFirstBalance ()

qqNotUniversal : QQSatisfied violatingCounts → ⊥
qqNotUniversal q = violatingCountsFailFirstBalance (QQSatisfied.firstBalance q)

record QuantumLikeDecisionBoundary : Set where
  constructor quantumLikeDecisionBoundary
  field
    quantumFormalismImpliesQuantumBrain : Bool
    qqEqualityIsUniversalDecisionLaw : Bool
    updateNoncommutativityImpliesObservableNoncommutativity : Bool

canonicalQuantumLikeDecisionBoundary : QuantumLikeDecisionBoundary
canonicalQuantumLikeDecisionBoundary =
  quantumLikeDecisionBoundary false false false
