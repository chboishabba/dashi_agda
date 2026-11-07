{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21ConwayTotalChainExact where

------------------------------------------------------------------------
-- K01: TOTAL FINITE CONWAY CHAIN EVALUATOR.
--
-- Conway 2001 chain rules for positive entries:
-- [a,b] = a^b,
-- X -> p -> 1 = X -> p,
-- X -> 1 -> q = X,
-- X -> (p+1) -> (q+1)
--   = X -> (X -> p -> (q+1)) -> q   (p,q >= 1).
--
-- Instead of illegal nested recursion on a possibly growing argument,
-- retain a prefix as (value of X, extension t |-> value of X->t).
-- For a fixed prefix X and q>1, the recurrence in p is finite
-- iteration of the q-1 function, starting at value(X).
-- Recursion on q is strictly structural. Then fold finite prefixes.
--
-- This is a total Nat evaluator and a typed positive-only entrypoint.
-- It is NOT a polynomial-time evaluation algorithm or a P!=NP proof.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (_++_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)
import Data.Nat.Properties as NatP

power : Nat → Nat → Nat
power a zero = 1
power a (suc n) = a * power a n

iterate : (Nat → Nat) → Nat → Nat → Nat
iterate f zero seed = seed
iterate f (suc n) seed = f (iterate f n seed)

-- q is the last arrow argument, p is penultimate.
-- Zero inputs belong only to the total parser's non-Conway fallback.
chainStep : Nat → (Nat → Nat) → Nat → Nat → Nat
chainStep value extension zero p = value
chainStep value extension (suc zero) p = extension p
chainStep value extension (suc (suc q)) zero = value
chainStep value extension (suc (suc q)) (suc p) =
  iterate
    (λ k → chainStep value extension (suc q) k)
    p value

-- The original terminal-1 and embedded-1 rules.
terminalOne :
  (value : Nat) (extension : Nat → Nat) (p : Nat) →
  chainStep value extension 1 p ≡ extension p
terminalOne value extension p = refl

embeddedOne :
  (value : Nat) (extension : Nat → Nat) (q : Nat) →
  chainStep value extension (suc (suc q)) 1 ≡ value
embeddedOne value extension q = refl

-- Conway's exact expansion for p,q>1.
chainRuleSix :
  (value : Nat) (extension : Nat → Nat) (p q : Nat) →
  chainStep value extension (suc (suc q)) (suc (suc p))
    ≡ chainStep value extension (suc q)
        (chainStep value extension (suc (suc q)) (suc p))
chainRuleSix value extension p q = refl

record Prefix : Set where
  constructor prefix
  field
    value : Nat
    extension : Nat → Nat
open Prefix public

start : Nat → Prefix
start a = prefix a (power a)

push : Prefix → Nat → Prefix
push (prefix v ext) p =
  prefix (ext p) (λ q → chainStep v ext q p)

run : Prefix → List Nat → Nat
run state [] = value state
run state (n ∷ rest) = run (push state n) rest

evaluate : List Nat → Nat
evaluate [] = 1
evaluate (a ∷ rest) = run (start a) rest

-- Positive inputs can be formed without a runtime nonzero assumption.
data Positive : Set where
  positive : Nat → Positive

asNat : Positive → Nat
asNat (positive n) = suc n

positiveEntries : List Positive → List Nat
positiveEntries [] = []
positiveEntries (p ∷ ps) = asNat p ∷ positiveEntries ps

evaluatePositive : List Positive → Nat
evaluatePositive entries = evaluate (positiveEntries entries)

emptyEntry : evaluate [] ≡ 1
emptyEntry = refl

oneEntry : (a : Nat) → evaluate (a ∷ []) ≡ a
oneEntry a = refl

twoEntries :
  (a b : Nat) → evaluate (a ∷ b ∷ []) ≡ power a b
twoEntries a b = refl

threeEntries :
  (a b c : Nat) →
  evaluate (a ∷ b ∷ c ∷ [])
    ≡ chainStep a (power a) c b
threeEntries a b c = refl

------------------------------------------------------------------------
-- Universal rule-five tail elimination. The extension invariant at 1
-- holds for every reachable prefix. Once a 1 has been appended,
-- its successor state is constant on ALL future arguments.
------------------------------------------------------------------------

iterateConstant :
  (f : Nat → Nat) (v n : Nat) →
  ((k : Nat) → f k ≡ v) →
  iterate f n v ≡ v
iterateConstant f v zero constant = refl
iterateConstant f v (suc n) constant
  rewrite iterateConstant f v n constant = constant v

stepConstant :
  (v : Nat) (ext : Nat → Nat) →
  ((k : Nat) → ext k ≡ v) →
  (q p : Nat) →
  chainStep v ext q p ≡ v
stepConstant v ext constant zero p = refl
stepConstant v ext constant (suc zero) p = constant p
stepConstant v ext constant (suc (suc q)) zero = refl
stepConstant v ext constant (suc (suc q)) (suc p) =
  iterateConstant
    (λ k → chainStep v ext (suc q) k)
    v p
    (stepConstant v ext constant (suc q))

startOneInvariant :
  (a : Nat) → extension (start a) 1 ≡ value (start a)
startOneInvariant a = NatP.*-identityʳ a

pushOneInvariant :
  (state : Prefix) (n : Nat) →
  extension (push state n) 1 ≡ value (push state n)
pushOneInvariant state n = refl

constantRun :
  (state : Prefix) →
  ((k : Nat) → extension state k ≡ value state) →
  (rest : List Nat) →
  run state rest ≡ value state
constantRun state constant [] = refl
constantRun (prefix v ext) constant (n ∷ rest) =
  trans
    (constantRun
      (push (prefix v ext) n)
      (λ q →
        trans
          (stepConstant v ext constant q n)
          (sym (constant n)))
      rest)
    (constant n)

pushOneConstant :
  (state : Prefix) →
  extension state 1 ≡ value state →
  (q : Nat) →
  extension (push state 1) q ≡ value state
pushOneConstant (prefix v ext) invariant zero = refl
pushOneConstant (prefix v ext) invariant (suc zero) = invariant
pushOneConstant (prefix v ext) invariant (suc (suc q)) = refl

dropAfterOne :
  (state : Prefix) →
  extension state 1 ≡ value state →
  (rest : List Nat) →
  run (push state 1) rest ≡ value state
dropAfterOne state invariant rest =
  trans
    (constantRun
      (push state 1)
      (λ q → trans
        (pushOneConstant state invariant q)
        (sym invariant))
      rest)
    invariant


------------------------------------------------------------------------
-- Publish the rule-five proof over ANY actual finite chain prefix,
-- not merely the private Prefix machine state.
------------------------------------------------------------------------

advance : Prefix → List Nat → Prefix
advance state [] = state
advance state (n ∷ rest) = advance (push state n) rest

runAdvance :
  (state : Prefix) (entries : List Nat) →
  run state entries ≡ value (advance state entries)
runAdvance state [] = refl
runAdvance state (n ∷ rest) =
  runAdvance (push state n) rest

runAppend :
  (state : Prefix) (pre post : List Nat) →
  run state (pre ++ post) ≡ run (advance state pre) post
runAppend state [] post = refl
runAppend state (n ∷ pre) post =
  runAppend (push state n) pre post

advanceOneInvariant :
  (state : Prefix) (entries : List Nat) →
  extension state 1 ≡ value state →
  extension (advance state entries) 1
    ≡ value (advance state entries)
advanceOneInvariant state [] invariant = invariant
advanceOneInvariant state (n ∷ rest) invariant =
  advanceOneInvariant (push state n) rest
    (pushOneInvariant state n)

conwayDropAfterInternalOne :
  (a : Nat) (before after : List Nat) →
  evaluate (a ∷ (before ++ (1 ∷ after)))
    ≡ evaluate (a ∷ before)
conwayDropAfterInternalOne a before after =
  trans
    (runAppend (start a) before (1 ∷ after))
    (trans
      (dropAfterOne (advance (start a) before)
        (advanceOneInvariant (start a) before
          (startOneInvariant a)) after)
      (sym (runAdvance (start a) before)))

-- Concrete rules small enough for ordinary normalization.
twoThreeTwo : evaluate (2 ∷ 3 ∷ 2 ∷ []) ≡ 16
twoThreeTwo = refl

threeTwoTwo : evaluate (3 ∷ 2 ∷ 2 ∷ []) ≡ 27
threeTwoTwo = refl

-- The source's rule 5 also drops everything after a 1. The prefix
-- extension invariant extension 1 = value makes that hold under folding.
--
-- The higher chain is intentionally retained symbolically.
-- Reducing [2,3,2,2] to a fully evaluated Nat during kernel checking
-- would be impractical; chainRuleSix is its universal derivation rule.
