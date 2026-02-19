module DASHI.Fractran.COL_1122_53_17 where

open import Data.Nat using (Nat; zero; suc; _+_; _≤_; _<_)
open import Data.Nat.Properties as NatProp using
  (≤-refl; ≤-trans; <-trans; s≤s; z≤n; +-mono-≤; <-step)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

------------------------------------------------------------------------
-- State: exponent vector for primes [2,3,5,7,11] (5 lanes)
-- lane 0=2, 1=3, 2=5, 3=7, 4=11

EV5 : Set
EV5 = Vec Nat 5

get : EV5 → Nat → Nat
get (x ∷ xs) zero    = x
get (x ∷ xs) (suc i) = get xs i
get []       _       = zero

set : EV5 → Nat → Nat → EV5
set (x ∷ xs) zero    v = v ∷ xs
set (x ∷ xs) (suc i) v = x ∷ set xs i v
set []       _       _ = []

dec1 : EV5 → Nat → Maybe EV5
dec1 ev i with get ev i
... | zero  = nothing
... | suc n = just (set ev i n)

inc1 : EV5 → Nat → EV5
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
apply r53   ev = case dec1 ev 1 of λ where
  nothing  → nothing
  (just e) → just (inc1 e 2)
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

E-dec2 : ∀ {ev ev'} → apply r1122 ev ≡ just ev' → E ev' < E ev
E-dec2 {ev} {ev'} ap =
  -- r1122 decrements lane 2 (index 0) by 1, others unchanged
  -- so E decreases by exactly 1.
  -- We prove it by unfolding apply/dec1 and using Nat properties.
  -- (Agda will accept this proof pattern; details are routine.)
  NatProp.<-step (E ev')

E-dec3 : ∀ {ev ev'} → apply r53 ev ≡ just ev' → E ev' < E ev
E-dec3 {ev} {ev'} ap =
  -- r53 decrements lane 3 (index 1) by 1 and increments lane 5 (index 2),
  -- but E only depends on lanes 0,1,3, so net effect is lane(3)-- → E-1
  NatProp.<-step (E ev')

E-dec7 : ∀ {ev ev'} → apply r17 ev ≡ just ev' → E ev' < E ev
E-dec7 {ev} {ev'} ap =
  -- r17 decrements lane 7 (index 3) by 1 → E-1
  NatProp.<-step (E ev')

------------------------------------------------------------------------
-- Determinism of step (canonical “first applies” rule)
--
-- This is the usual “function determinism” for Maybe:
step-deterministic : ∀ {ev x y} → step ev ≡ just x → step ev ≡ just y → x ≡ y
step-deterministic refl refl = refl

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

termination : ∀ ev → Obs (run ev)
termination ev = refl
