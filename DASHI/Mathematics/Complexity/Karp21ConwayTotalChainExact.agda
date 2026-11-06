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
open import Agda.Builtin.Equality using (_≡_; refl)

power : Nat → Nat → Nat
power a zero = 1
power a (suc n) = a * power a n

iterate : (Nat → Nat) → Nat → Nat → Nat
iterate f zero seed = seed
iterate f (suc n) seed = f (iterate f n seed)

-- q is the last arrow argument, p is penultimate.
-- Zero inputs belong only to the total parser's non-Conway fallback.
chainStep : Nat → (Nat → Nat) → Nat → Nat → Nat
chainStep value extension zero p = 0
chainStep value extension (suc zero) p = extension p
chainStep value extension (suc (suc q)) zero = 0
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
evaluate [] = 0
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

-- Concrete rules small enough for ordinary normalization.
twoThreeTwo : evaluate (2 ∷ 3 ∷ 2 ∷ []) ≡ 16
twoThreeTwo = refl

threeTwoTwo : evaluate (3 ∷ 2 ∷ 2 ∷ []) ≡ 27
threeTwoTwo = refl

-- The higher chain is intentionally retained symbolically.
-- Reducing [2,3,2,2] to a fully evaluated Nat during kernel checking
-- would be impractical; chainRuleSix is its universal derivation rule.
