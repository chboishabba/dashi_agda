module DASHI.Mathematics.Complexity.Karp21SATToThreeSATGadgetExact where

------------------------------------------------------------------------
-- ORIGINAL SOURCE: Stephen A. Cook (1971), "The Complexity of
-- Theorem-Proving Procedures", DOI 10.1145/800157.805047.
-- Richard M. Karp (1972), p. 98, cites Cook's 3-literal reduction.
--
-- DASHI proof ownership: explicit 4->3 local Boolean clause splitter.
-- This one *unconditional, constructive* gadget is not the complete
-- recursive SAT -> 3-SAT map or its polynomial machine-clock proof.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (Σ; _,_)

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR

orBool : Bool → Bool → Bool
orBool true _ = true
orBool false value = value

andBool : Bool → Bool → Bool
andBool true value = value
andBool false _ = false

notBool : Bool → Bool
notBool true = false
notBool false = true

fourLiteralClause : Bool → Bool → Bool → Bool → Bool
fourLiteralClause a b c d = orBool a (orBool b (orBool c d))

-- (a or b or x) and (not x or c or d).
twoThreeLiteralClauses :
  Bool → Bool → Bool → Bool → Bool → Bool
twoThreeLiteralClauses a b c d x =
  andBool
    (orBool a (orBool b x))
    (orBool (notBool x) (orBool c d))

complementOrTrue : (value : Bool) →
  orBool (notBool value) value ≡ true
complementOrTrue false = refl
complementOrTrue true = refl

fourToThreeWitness :
  (a b c d : Bool) →
  fourLiteralClause a b c d ≡ true →
  Σ Bool (λ fresh → twoThreeLiteralClauses a b c d fresh ≡ true)
fourToThreeWitness a b c d accepted =
  orBool c d , witnessed
  where
    witnessed :
      twoThreeLiteralClauses a b c d (orBool c d) ≡ true
    witnessed rewrite accepted | complementOrTrue (orBool c d) = refl

threeToFourWitness :
  (a b c d fresh : Bool) →
  twoThreeLiteralClauses a b c d fresh ≡ true →
  fourLiteralClause a b c d ≡ true
threeToFourWitness true b c d fresh accepted = refl
threeToFourWitness false true c d fresh accepted = refl
threeToFourWitness false false true d fresh accepted = refl
threeToFourWitness false false false true fresh accepted = refl
threeToFourWitness false false false false false ()
threeToFourWitness false false false false true ()

cookKarpFourToThreeClauseIff :
  (a b c d : Bool) →
  PR.Iff
    (fourLiteralClause a b c d ≡ true)
    (Σ Bool (λ fresh → twoThreeLiteralClauses a b c d fresh ≡ true))
cookKarpFourToThreeClauseIff a b c d =
  PR.iff
    (fourToThreeWitness a b c d)
    (λ (fresh , valid) → threeToFourWitness a b c d fresh valid)
