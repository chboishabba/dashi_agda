module DASHI.Mathematics.Complexity.FixedWidthCNFToCookFormulaExact where

------------------------------------------------------------------------
-- FIXED-WIDTH CNF -> CLAY-CRITICAL COOK BOOLEANFORMULA
--
-- The concrete tape Cook--Levin development uses:
--
--   FixedWidthTruthTableCNFExact.CNF n
--
-- while the Clay-critical SAT lane uses:
--
--   CookLevinCircuitGCTBoundary.BooleanFormula.
--
-- This owner gives the literal semantics-preserving compiler:
--
--   positive i  -> x_i
--   negative i  -> not x_i
--   clause      -> OR tree, false for []
--   CNF         -> AND tree, true for [].
--
-- Main results:
--
--   evaluate(cnfToCook F, bitsAssignment b)
--     = evaluateCNF(F,b)
--
-- and for EVERY arbitrary Cook assignment A:
--
--   evaluate(cnfToCook F,A)
--     = evaluateCNF(F,bitsFromAssignment A).
--
-- Therefore CNF satisfiability and Cook satisfiability are equivalent.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base as Fin using (Fin; toℕ)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

------------------------------------------------------------------------
-- Boolean-operation agreement.
------------------------------------------------------------------------

notAgreement :
  (value : Bool) →
  Cook.notBool value ≡ CNF.notBool value
notAgreement false = refl
notAgreement true = refl

orAgreement :
  (left right : Bool) →
  Cook.orBool left right
  ≡ CNF.orBool left right
orAgreement false right = refl
orAgreement true right = refl

andAgreement :
  (left right : Bool) →
  Cook.andBool left right
  ≡ CNF.andBool left right
andAgreement false right = refl
andAgreement true right = refl

------------------------------------------------------------------------
-- Literal / clause / CNF compiler.
------------------------------------------------------------------------

literalToCook :
  ∀ {width : Nat} →
  CNF.Literal width →
  Cook.BooleanFormula
literalToCook (CNF.positive index) =
  Cook.variable (Fin.toℕ index)
literalToCook (CNF.negative index) =
  Cook.negate
    (Cook.variable (Fin.toℕ index))

clauseToCook :
  ∀ {width : Nat} →
  CNF.Clause width →
  Cook.BooleanFormula
clauseToCook [] =
  Cook.constant false
clauseToCook (literal ∷ literals) =
  Cook.disjunction
    (literalToCook literal)
    (clauseToCook literals)

cnfToCook :
  ∀ {width : Nat} →
  CNF.CNF width →
  Cook.BooleanFormula
cnfToCook [] =
  Cook.constant true
cnfToCook (clause ∷ clauses) =
  Cook.conjunction
    (clauseToCook clause)
    (cnfToCook clauses)

------------------------------------------------------------------------
-- Bit-vector -> total Nat assignment.
------------------------------------------------------------------------

lookupNatBit :
  ∀ {width : Nat} →
  Nat →
  CNF.Bits width →
  Bool
lookupNatBit index CNF.[]ᵇ =
  false
lookupNatBit zero (bit CNF.∷ᵇ bits) =
  bit
lookupNatBit (suc index) (bit CNF.∷ᵇ bits) =
  lookupNatBit index bits

lookupNatBitAtFin :
  ∀ {width : Nat}
    (bits : CNF.Bits width)
    (index : Fin width) →
  lookupNatBit
    (Fin.toℕ index)
    bits
  ≡
  CNF.lookupBit bits index
lookupNatBitAtFin
    (bit CNF.∷ᵇ bits)
    Fin.zero =
  refl
lookupNatBitAtFin
    (bit CNF.∷ᵇ bits)
    (Fin.suc index) =
  lookupNatBitAtFin
    bits
    index

bitsAssignment :
  ∀ {width : Nat} →
  CNF.Bits width →
  Cook.Assignment
bitsAssignment bits index =
  lookupNatBit index bits

------------------------------------------------------------------------
-- Evaluation equivalence on a supplied finite bit vector.
------------------------------------------------------------------------

literalEvaluationOnBits :
  ∀ {width : Nat}
    (literal : CNF.Literal width)
    (bits : CNF.Bits width) →
  Cook.evaluate
    (literalToCook literal)
    (bitsAssignment bits)
  ≡
  CNF.evaluateLiteral
    literal
    bits
literalEvaluationOnBits
    (CNF.positive index)
    bits =
  lookupNatBitAtFin bits index
literalEvaluationOnBits
    (CNF.negative index)
    bits =
  trans
    (cong
      Cook.notBool
      (lookupNatBitAtFin bits index))
    (notAgreement
      (CNF.lookupBit bits index))

clauseEvaluationOnBits :
  ∀ {width : Nat}
    (clause : CNF.Clause width)
    (bits : CNF.Bits width) →
  Cook.evaluate
    (clauseToCook clause)
    (bitsAssignment bits)
  ≡
  CNF.evaluateClause
    clause
    bits
clauseEvaluationOnBits [] bits =
  refl
clauseEvaluationOnBits
    (literal ∷ literals)
    bits =
  trans
    (cong₂
      Cook.orBool
      (literalEvaluationOnBits literal bits)
      (clauseEvaluationOnBits literals bits))
    (orAgreement
      (CNF.evaluateLiteral literal bits)
      (CNF.evaluateClause literals bits))

cnfEvaluationOnBits :
  ∀ {width : Nat}
    (formula : CNF.CNF width)
    (bits : CNF.Bits width) →
  Cook.evaluate
    (cnfToCook formula)
    (bitsAssignment bits)
  ≡
  CNF.evaluateCNF
    formula
    bits
cnfEvaluationOnBits [] bits =
  refl
cnfEvaluationOnBits
    (clause ∷ clauses)
    bits =
  trans
    (cong₂
      Cook.andBool
      (clauseEvaluationOnBits clause bits)
      (cnfEvaluationOnBits clauses bits))
    (andAgreement
      (CNF.evaluateClause clause bits)
      (CNF.evaluateCNF clauses bits))

------------------------------------------------------------------------
-- Arbitrary Cook assignment -> finite width bit vector.
------------------------------------------------------------------------

bitsFromAssignment :
  (width : Nat) →
  Cook.Assignment →
  CNF.Bits width
bitsFromAssignment zero assignment =
  CNF.[]ᵇ
bitsFromAssignment (suc width) assignment =
  assignment zero
  CNF.∷ᵇ
  bitsFromAssignment
    width
    (λ index → assignment (suc index))

lookupBitsFromAssignment :
  ∀ {width : Nat}
    (assignment : Cook.Assignment)
    (index : Fin width) →
  CNF.lookupBit
    (bitsFromAssignment width assignment)
    index
  ≡
  assignment (Fin.toℕ index)
lookupBitsFromAssignment
    {suc width}
    assignment
    Fin.zero =
  refl
lookupBitsFromAssignment
    {suc width}
    assignment
    (Fin.suc index) =
  lookupBitsFromAssignment
    (λ inner → assignment (suc inner))
    index

------------------------------------------------------------------------
-- Evaluation equivalence from an arbitrary Cook assignment.
------------------------------------------------------------------------

literalEvaluationFromAssignment :
  ∀ {width : Nat}
    (literal : CNF.Literal width)
    (assignment : Cook.Assignment) →
  Cook.evaluate
    (literalToCook literal)
    assignment
  ≡
  CNF.evaluateLiteral
    literal
    (bitsFromAssignment width assignment)
literalEvaluationFromAssignment
    (CNF.positive index)
    assignment =
  sym
    (lookupBitsFromAssignment
      assignment
      index)
literalEvaluationFromAssignment
    (CNF.negative index)
    assignment =
  trans
    (cong
      Cook.notBool
      (sym
        (lookupBitsFromAssignment
          assignment
          index)))
    (notAgreement
      (CNF.lookupBit
        (bitsFromAssignment _ assignment)
        index))

clauseEvaluationFromAssignment :
  ∀ {width : Nat}
    (clause : CNF.Clause width)
    (assignment : Cook.Assignment) →
  Cook.evaluate
    (clauseToCook clause)
    assignment
  ≡
  CNF.evaluateClause
    clause
    (bitsFromAssignment width assignment)
clauseEvaluationFromAssignment [] assignment =
  refl
clauseEvaluationFromAssignment
    (literal ∷ literals)
    assignment =
  trans
    (cong₂
      Cook.orBool
      (literalEvaluationFromAssignment
        literal assignment)
      (clauseEvaluationFromAssignment
        literals assignment))
    (orAgreement
      (CNF.evaluateLiteral
        literal
        (bitsFromAssignment _ assignment))
      (CNF.evaluateClause
        literals
        (bitsFromAssignment _ assignment)))

cnfEvaluationFromAssignment :
  ∀ {width : Nat}
    (formula : CNF.CNF width)
    (assignment : Cook.Assignment) →
  Cook.evaluate
    (cnfToCook formula)
    assignment
  ≡
  CNF.evaluateCNF
    formula
    (bitsFromAssignment width assignment)
cnfEvaluationFromAssignment [] assignment =
  refl
cnfEvaluationFromAssignment
    (clause ∷ clauses)
    assignment =
  trans
    (cong₂
      Cook.andBool
      (clauseEvaluationFromAssignment
        clause assignment)
      (cnfEvaluationFromAssignment
        clauses assignment))
    (andAgreement
      (CNF.evaluateClause
        clause
        (bitsFromAssignment _ assignment))
      (CNF.evaluateCNF
        clauses
        (bitsFromAssignment _ assignment)))

------------------------------------------------------------------------
-- Exact satisfiability transport.
------------------------------------------------------------------------

cnfWitnessGivesCookSatisfiable :
  ∀ {width : Nat}
    (formula : CNF.CNF width)
    (bits : CNF.Bits width) →
  CNF.evaluateCNF formula bits ≡ true →
  Cook.Satisfiable
    (cnfToCook formula)
cnfWitnessGivesCookSatisfiable
    formula
    bits
    accepted =
  Cook.satisfyingAssignment
    (bitsAssignment bits)
    (trans
      (cnfEvaluationOnBits
        formula
        bits)
      accepted)

cookSatisfiableGivesCNFWitness :
  ∀ {width : Nat}
    (formula : CNF.CNF width) →
  Cook.Satisfiable
    (cnfToCook formula) →
  Σ (CNF.Bits width)
    (λ bits →
      CNF.evaluateCNF formula bits ≡ true)
cookSatisfiableGivesCNFWitness
    {width}
    formula
    (Cook.satisfyingAssignment
      assignment
      accepted) =
  bitsFromAssignment width assignment
  ,
  trans
    (sym
      (cnfEvaluationFromAssignment
        formula
        assignment))
    accepted

------------------------------------------------------------------------
-- Exact bridge package.
------------------------------------------------------------------------

record CNFCookSatisfiabilityExact
    {width : Nat}
    (formula : CNF.CNF width) : Set₁ where
  constructor cnf-cook-satisfiability-exact
  field
    cnfToCookSAT :
      (bits : CNF.Bits width) →
      CNF.evaluateCNF formula bits ≡ true →
      Cook.Satisfiable
        (cnfToCook formula)

    cookSATToCNF :
      Cook.Satisfiable
        (cnfToCook formula) →
      Σ (CNF.Bits width)
        (λ bits →
          CNF.evaluateCNF formula bits ≡ true)

open CNFCookSatisfiabilityExact public

cnfCookSatisfiabilityExact :
  ∀ {width : Nat}
    (formula : CNF.CNF width) →
  CNFCookSatisfiabilityExact formula
cnfCookSatisfiabilityExact formula =
  cnf-cook-satisfiability-exact
    (cnfWitnessGivesCookSatisfiable formula)
    (cookSatisfiableGivesCNFWitness formula)

------------------------------------------------------------------------
-- Research consequence.
--
-- Every concrete-tape global Cook--Levin CNF can now be transported to the
-- exact Cook.BooleanFormula carrier consumed by SATLowerBoundProducer without
-- losing satisfiability semantics.
------------------------------------------------------------------------
