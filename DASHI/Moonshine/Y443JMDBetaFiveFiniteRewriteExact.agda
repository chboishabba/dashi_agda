module DASHI.Moonshine.Y443JMDBetaFiveFiniteRewriteExact where

------------------------------------------------------------------------
-- Golden finite Coxeter rewrite certificate for JMD beta^5.
-- Authoritative mathematical group proof: JMD/CFSGCorollary Y443.lean.
--
-- The true word beta = x5 x6 x7 x8, so beta^5 has 20 letters.
-- This native Agda finite machine checks a 35-step sequence of:
--  15 distant commutations (m=2),
--  10 adjacent braid moves (m=3),
--  10 x_i^2 cancellations.
-- Every move is checked against the ACTUAL 4-node path adjacency.
--
-- Finite syntax proof is distinct from the group semantic bridge
-- interpreting the braid moves via the selected Y443 group relators.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

data Gen : Set where
  x5 x6 x7 x8 : Gen

eqG : Gen → Gen → Bool
eqG x5 x5 = true
eqG x6 x6 = true
eqG x7 x7 = true
eqG x8 x8 = true
eqG _ _ = false

adjG : Gen → Gen → Bool
adjG x5 x6 = true
adjG x6 x5 = true
adjG x6 x7 = true
adjG x7 x6 = true
adjG x7 x8 = true
adjG x8 x7 = true
adjG _ _ = false

andB : Bool → Bool → Bool
andB true true = true
andB _ _ = false

notB : Bool → Bool
notB true = false
notB false = true

canCommute : Gen → Gen → Bool
canCommute a b = andB (notB (eqG a b)) (notB (adjG a b))

canBraid : Gen → Gen → Gen → Bool
canBraid a b c = andB (eqG a c) (adjG a b)

data Kind : Set where
  commute braid cancel : Kind

record Operation : Set where
  constructor operation
  field
    kind : Kind
    position : Nat

open Operation public

Word : Set
Word = List Gen

validLocal : Kind → Word → Bool
validLocal cancel (a ∷ b ∷ _) = eqG a b
validLocal commute (a ∷ b ∷ _) = canCommute a b
validLocal braid (a ∷ b ∷ c ∷ _) = canBraid a b c
validLocal _ _ = false

rewriteLocal : Kind → Word → Word
rewriteLocal cancel (a ∷ b ∷ rest) with eqG a b
... | true = rest
... | false = a ∷ b ∷ rest
rewriteLocal commute (a ∷ b ∷ rest) with canCommute a b
... | true = b ∷ a ∷ rest
... | false = a ∷ b ∷ rest
rewriteLocal braid (a ∷ b ∷ c ∷ rest) with canBraid a b c
... | true = b ∷ a ∷ b ∷ rest
... | false = a ∷ b ∷ c ∷ rest
rewriteLocal _ word = word

validAt : Nat → Kind → Word → Bool
validAt zero rule word = validLocal rule word
validAt (suc n) rule [] = false
validAt (suc n) rule (_ ∷ rest) = validAt n rule rest

stepAt : Nat → Kind → Word → Word
stepAt zero rule word = rewriteLocal rule word
stepAt (suc n) rule [] = []
stepAt (suc n) rule (x ∷ rest) = x ∷ stepAt n rule rest

step : Operation → Word → Word
step op = stepAt (position op) (kind op)

operations : List Operation
operations =
  operation commute 3 ∷
  operation commute 2 ∷
  operation commute 4 ∷
  operation braid 0 ∷
  operation braid 2 ∷
  operation braid 4 ∷
  operation cancel 6 ∷
  operation commute 1 ∷
  operation commute 3 ∷
  operation commute 2 ∷
  operation commute 5 ∷
  operation braid 3 ∷
  operation braid 5 ∷
  operation cancel 7 ∷
  operation commute 4 ∷
  operation commute 6 ∷
  operation commute 5 ∷
  operation braid 6 ∷
  operation cancel 8 ∷
  operation commute 7 ∷
  operation commute 8 ∷
  operation cancel 9 ∷
  operation commute 2 ∷
  operation braid 0 ∷
  operation braid 2 ∷
  operation cancel 4 ∷
  operation commute 1 ∷
  operation braid 2 ∷
  operation cancel 4 ∷
  operation commute 3 ∷
  operation cancel 4 ∷
  operation braid 0 ∷
  operation cancel 2 ∷
  operation cancel 1 ∷
  operation cancel 0 ∷ []

run : Word → List Operation → Word
run word [] = word
run word (op ∷ ops) = run (step op word) ops

everyStepValid : Word → List Operation → Bool
everyStepValid word [] = true
everyStepValid word (op ∷ ops) =
  andB (validAt (position op) (kind op) word)
       (everyStepValid (step op word) ops)

count : List Operation → Nat
count [] = 0
count (_ ∷ xs) = suc (count xs)

beta : Word
beta = x5 ∷ x6 ∷ x7 ∷ x8 ∷ []

append : Word → Word → Word
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

powerWord : Word → Nat → Word
powerWord word zero = []
powerWord word (suc n) = append word (powerWord word n)

betaToFifth : Word
betaToFifth = powerWord beta 5

betaFifthAllThirtyFiveMovesValid :
  everyStepValid betaToFifth operations ≡ true
betaFifthAllThirtyFiveMovesValid = refl

betaFifthReducesToEmpty :
  run betaToFifth operations ≡ []
betaFifthReducesToEmpty = refl

numberOfRewriteMoves : count operations ≡ 35
numberOfRewriteMoves = refl

-- A group-semantics soundness theorem can now consume this exact
-- validated certificate. No claim that syntactic reduction alone
-- supplies the selected Monster/VOA group interpretation.
