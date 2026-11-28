module DASHI.Mathematics.Complexity.PNPCompactOccurrenceDecisionGainExact where

-- Original Cook formula -> first-occurrence indexed chart -> actual
-- candidate self-reduction -> original finite witness reopening.
-- Reuse Karp21CookFiniteOccurrenceWitnessExact: do not enumerate Nat
-- labels up to their numerical maximum or split repeated occurrences.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Fin.Base as Fin using (Fin)
open import Data.Nat.Base using (_≤_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
import Data.Nat.Properties as NatP
import DASHI.Mathematics.Complexity.Karp21CookFiniteOccurrenceWitnessExact as K
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNPDecisionDerivedGainFailureExact as Gain
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact as Prefix
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word

lookupNat : (xs : List Nat) → Fin (length xs) → Nat
lookupNat [] ()
lookupNat (j ∷ js) Fin.zero = j
lookupNat (j ∷ js) (Fin.suc k) = lookupNat js k

firstFin : (xs : List Nat) (i : Nat) → K._∈_ i xs → Fin (length xs)
firstFin [] i ()
firstFin (j ∷ js) i h with NatP._≟_ i j
... | yes e = Fin.zero
... | no ne with h
...   | K.here = ⊥-elim (ne refl)
...   | K.there m = Fin.suc (firstFin js i m)

lookupFirst : (xs : List Nat) (i : Nat) (h : K._∈_ i xs) →
  lookupNat xs (firstFin xs i h) ≡ i
lookupFirst [] i ()
lookupFirst (j ∷ js) i h with NatP._≟_ i j
... | yes e = sym e
... | no ne with h
...   | K.here = ⊥-elim (ne refl)
...   | K.there m = lookupFirst js i m

bits : ∀ {n} → SAT.Assignment n → List Bool
bits {zero} x = []
bits {suc n} x = x Fin.zero ∷ bits (λ i → x (Fin.suc i))

reopen : (xs : List Nat) → SAT.Assignment (length xs) → Cook.Assignment
reopen xs x = K.recoverAssignment (K.pairObservations xs (bits x))

reopenFirst : (xs : List Nat) (x : SAT.Assignment (length xs))
  (i : Nat) (h : K._∈_ i xs) → reopen xs x i ≡ x (firstFin xs i h)
reopenFirst [] x i ()
reopenFirst (j ∷ js) x i h with NatP._≟_ i j
... | yes e = refl
... | no ne with h
...   | K.here = ⊥-elim (ne refl)
...   | K.there m = reopenFirst js (λ k → x (Fin.suc k)) i m

Cover : List Nat → Cook.BooleanFormula → Set
Cover xs f = ∀ i → K.Appears i f → K._∈_ i xs

compactWith : (xs : List Nat) (f : Cook.BooleanFormula) →
  Cover xs f → SAT.BooleanFormula (length xs)
compactWith xs (Cook.formulaVar i) h =
  SAT.formulaVar (firstFin xs i (h i K.atVariable))
compactWith xs (Cook.constant b) h = SAT.constant b
compactWith xs (Cook.negate f) h =
  SAT.negate (compactWith xs f (λ i a → h i (K.underNegation a)))
compactWith xs (Cook.conjunction f g) h =
  SAT.conjunction
    (compactWith xs f (λ i a → h i (K.inConjunctionLeft a)))
    (compactWith xs g (λ i a → h i (K.inConjunctionRight a)))
compactWith xs (Cook.disjunction f g) h =
  SAT.disjunction
    (compactWith xs f (λ i a → h i (K.inDisjunctionLeft a)))
    (compactWith xs g (λ i a → h i (K.inDisjunctionRight a)))

compactEvaluation : (xs : List Nat) (f : Cook.BooleanFormula)
  (h : Cover xs f) (x : SAT.Assignment (length xs)) (a : Cook.Assignment) →
  (∀ i (p : K.Appears i f) → x (firstFin xs i (h i p)) ≡ a i) →
  SAT.evaluate (compactWith xs f h) x ≡ Cook.evaluate f a
compactEvaluation xs (Cook.formulaVar i) h x a eq = eq i K.atVariable
compactEvaluation xs (Cook.constant b) h x a eq = refl
compactEvaluation xs (Cook.negate f) h x a eq =
  trans (cong SAT.notBool
    (compactEvaluation xs f (λ i p → h i (K.underNegation p)) x a
      (λ i p → eq i (K.underNegation p))))
    (Bridge.notBoolAgreement (Cook.evaluate f a))
compactEvaluation xs (Cook.conjunction f g) h x a eq =
  trans (cong₂ SAT.andBool
    (compactEvaluation xs f (λ i p → h i (K.inConjunctionLeft p)) x a
      (λ i p → eq i (K.inConjunctionLeft p)))
    (compactEvaluation xs g (λ i p → h i (K.inConjunctionRight p)) x a
      (λ i p → eq i (K.inConjunctionRight p))))
    (Bridge.andBoolAgreement (Cook.evaluate f a) (Cook.evaluate g a))
compactEvaluation xs (Cook.disjunction f g) h x a eq =
  trans (cong₂ SAT.orBool
    (compactEvaluation xs f (λ i p → h i (K.inDisjunctionLeft p)) x a
      (λ i p → eq i (K.inDisjunctionLeft p)))
    (compactEvaluation xs g (λ i p → h i (K.inDisjunctionRight p)) x a
      (λ i p → eq i (K.inDisjunctionRight p))))
    (Bridge.orBoolAgreement (Cook.evaluate f a) (Cook.evaluate g a))

canonicalCover : (f : Cook.BooleanFormula) → Cover (K.formulaVariables f) f
canonicalCover f i p = K.appearsInVariableList p

compact : (f : Cook.BooleanFormula) →
  SAT.BooleanFormula (length (K.formulaVariables f))
compact f = compactWith (K.formulaVariables f) f (canonicalCover f)

project : (f : Cook.BooleanFormula) → Cook.Assignment →
  SAT.Assignment (length (K.formulaVariables f))
project f a i = a (lookupNat (K.formulaVariables f) i)

projectExact : (f : Cook.BooleanFormula) (a : Cook.Assignment) →
  SAT.evaluate (compact f) (project f a) ≡ Cook.evaluate f a
projectExact f a =
  compactEvaluation (K.formulaVariables f) f (canonicalCover f) (project f a) a
    (λ i p → cong a (lookupFirst (K.formulaVariables f) i (canonicalCover f i p)))

reopenExact : (f : Cook.BooleanFormula)
  (x : SAT.Assignment (length (K.formulaVariables f))) →
  SAT.evaluate (compact f) x ≡ Cook.evaluate f (reopen (K.formulaVariables f) x)
reopenExact f x =
  compactEvaluation (K.formulaVariables f) f (canonicalCover f) x
    (reopen (K.formulaVariables f) x)
    (λ i p → sym (reopenFirst (K.formulaVariables f) x i (canonicalCover f i p)))

toCompactSat : (f : Cook.BooleanFormula) → Cook.Satisfiable f → SAT.Satisfying (compact f)
toCompactSat f (Cook.satisfyingAssignment a h) =
  SAT.satisfying (project f a) (trans (projectExact f a) h)

fromCompactSat : (f : Cook.BooleanFormula) → SAT.Satisfying (compact f) → Cook.Satisfiable f
fromCompactSat f (SAT.satisfying x h) =
  Cook.satisfyingAssignment (reopen (K.formulaVariables f) x) (trans (sym (reopenExact f x)) h)

candidateWitness : ∀ {cost} → Gain.Candidate cost →
  Cook.BooleanFormula → Cook.Assignment
candidateWitness c f = reopen (K.formulaVariables f) (Gain.assignment c (compact f))

candidateMissGivesFailure : ∀ {cost} (c : Gain.Candidate cost) (f : Cook.BooleanFormula) →
  Cook.Satisfiable f → Cook.evaluate f (candidateWitness c f) ≡ false →
  Direct.SATDecisionFailure c
candidateMissGivesFailure c f sat miss =
  Gain.missGivesActualDecisionFailure c (compact f) (toCompactSat f sat)
    (trans (reopenExact f (Gain.assignment c (compact f))) miss)

-- The number of remaining Boolean coordinates is the number of
-- original syntactic occurrences, not max label. Repeated occurrences
-- use the first matching coordinate and unused slots cause no change.
occurrenceBound : (f : Cook.BooleanFormula) →
  length (K.formulaVariables f) ≤ Word.encodingSize (Binary.encodeFormulaBits f)
occurrenceBound f rewrite K.canonicalCookFormulaWordSizeExact f =
  NatP.≤-trans (K.variableCountWithinCookTokenCount f)
    (K.cookTokenCountWithinTripleCode (Prefix.cookFormulaTokenCount f))

-- These queries are the actual renamed indexed formulas passed to
-- the same candidate. No invariance of its answer under renaming is
-- assumed. Source evaluation is reopened to the ORIGINAL formula.
-- Native runtime/bit-machine compilation remains a distinct receipt.
