module DASHI.Combinatorics.FractranCOL where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Nat.Properties as NatProp using
  (≤-refl; ≤-trans; <-trans; +-mono-≤; <-step)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

------------------------------------------------------------------------
-- State: exponent vector for primes [2,3,5,7,11] (5 lanes)
-- lane 0=2, 1=3, 2=5, 3=7, 4=11

EV5 : Set
EV5 = Vec Nat 5

get : ∀ {n} → Vec Nat n → Nat → Nat
get (x ∷ xs) zero    = x
get (x ∷ xs) (suc i) = get xs i
get []       _       = zero

set : ∀ {n} → Vec Nat n → Nat → Nat → Vec Nat n
set (x ∷ xs) zero    v = v ∷ xs
set (x ∷ xs) (suc i) v = x ∷ set xs i v
set []       _       _ = []

dec1 : ∀ {n} → Vec Nat n → Nat → Maybe (Vec Nat n)
dec1 {n} ev i with get ev i
... | zero  = nothing
... | suc m = just (set ev i m)

inc1 : ∀ {n} → Vec Nat n → Nat → Vec Nat n
inc1 ev i = set ev i (suc (get ev i))

------------------------------------------------------------------------
-- The program P = [11/22, 5/3, 1/7]
--
-- Interpreted on exponent vectors:
-- 11/22 ( = 1/2 ) : requires lane(2)>0, then lane(2)--
-- 5/3             : requires lane(3)>0, then lane(3)-- and lane(5)++
-- 1/7             : requires lane(7)>0, then lane(7)--

data Rule : Set where
  r1122 r53 r17 : Rule

apply : Rule → EV5 → Maybe EV5
apply r1122 ev = dec1 ev 0
apply r53   ev with dec1 ev 1
... | nothing = nothing
... | just e  = just (inc1 e 2)
apply r17   ev = dec1 ev 3

-- First-applicable (deterministic) scan order:
step : EV5 → Maybe EV5
step ev with apply r1122 ev
... | just ev' = just ev'
... | nothing with apply r53 ev
...   | just ev' = just ev'
...   | nothing  = apply r17 ev

Obs : EV5 → Set
Obs ev = step ev ≡ nothing

------------------------------------------------------------------------
-- Rank / energy: a + b + d where lanes are 2,3,7 (0,1,3)
E : EV5 → Nat
E ev = get ev 0 + get ev 1 + get ev 3

------------------------------------------------------------------------
-- Lemmas: each successful rule application decreases E by 1

postulate
  E-dec2 : ∀ {ev ev'} → apply r1122 ev ≡ just ev' → E ev' < E ev
  E-dec3 : ∀ {ev ev'} → apply r53 ev ≡ just ev' → E ev' < E ev
  E-dec7 : ∀ {ev ev'} → apply r17 ev ≡ just ev' → E ev' < E ev

postulate
  -- Determinism of step (canonical “first applies” rule)
  --
  -- This is the usual “function determinism” for Maybe:
  step-deterministic : ∀ {ev x y} → step ev ≡ just x → step ev ≡ just y → x ≡ y

------------------------------------------------------------------------
-- Fuelled evaluation: iterate step at most fuel times

iterate : Nat → (EV5 → Maybe EV5) → EV5 → EV5
iterate zero    f x = x
iterate (suc n) f x with f x
... | nothing  = x
... | just x'  = iterate n f x'

run : EV5 → EV5
run ev = iterate (E ev) step ev

------------------------------------------------------------------------
-- Key theorem: termination by strict descent of E
--
-- Informal statement:
--   Because every successful step reduces E by 1,
--   after E(ev) iterations you must be stuck (Obs).
--
-- We package it as: step (run ev) = nothing.

postulate
  -- This is the only “plumbing” lemma you may want to prove explicitly in your Prelude style:
  -- If step makes a move, E strictly decreases.
  step-decreases-E : ∀ {ev ev'} → step ev ≡ just ev' → E ev' < E ev

postulate
  termination : ∀ ev → Obs (run ev)
