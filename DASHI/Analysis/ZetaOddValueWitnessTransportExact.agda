module DASHI.Analysis.ZetaOddValueWitnessTransportExact where

------------------------------------------------------------------------
-- EXTERNAL SOURCE: W. Zudilin, arXiv:1801.09895.
-- A July 2026 Lean 4/Mathlib formalization reports irrationality of
-- at least one odd zeta value in {5,7,...,33}. Exact Lean declaration,
-- its repository revision, and the kernel-axiom audit are NOT admitted.
--
-- DASHI CONTRIBUTION: generic same-value witness transport only.
-- This does not prove the external theorem or identify actual zeta values.
-- Golden ratio comparison: BishopGoldenRatioCarrierExact and
-- QuadraticIrrationalSignedApproximationFibreExact separate rational
-- representations from genuine irrational targets. Neither establishes
-- any equality between the golden ratio and zeta values.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Data.Fin using (Fin; toℕ)

OddWindow : Set
OddWindow = Fin 15

oddArgument : OddWindow → Nat
oddArgument j = 5 + 2 * toℕ j

record ValueContext : Set₁ where
  field
    Value Rational : Set
    embedRational : Rational → Value
    leanValue bishopValue dashiValue : OddWindow → Value
    leanToBishop : (j : OddWindow) → leanValue j ≡ bishopValue j
    bishopToDashi : (j : OddWindow) → bishopValue j ≡ dashiValue j

open ValueContext

RationalAt : (context : ValueContext) →
  (OddWindow → Value context) → OddWindow → Set
RationalAt context f j =
  Σ (Rational context) (λ q → f j ≡ embedRational context q)

IrrationalAt : (context : ValueContext) →
  (OddWindow → Value context) → OddWindow → Set
IrrationalAt context f j = RationalAt context f j → ⊥

rationalBackwards :
  (context : ValueContext) →
  (f g : OddWindow → Value context) →
  (j : OddWindow) → f j ≡ g j →
  RationalAt context g j → RationalAt context f j
rationalBackwards context f g j equal (q , witness) =
  q , trans equal witness

irrationalForwards :
  (context : ValueContext) →
  (f g : OddWindow → Value context) →
  (j : OddWindow) → f j ≡ g j →
  IrrationalAt context f j → IrrationalAt context g j
irrationalForwards context f g j equal irrational rationalG =
  irrational (rationalBackwards context f g j equal rationalG)

irrationalBackwards :
  (context : ValueContext) →
  (f g : OddWindow → Value context) →
  (j : OddWindow) → f j ≡ g j →
  IrrationalAt context g j → IrrationalAt context f j
irrationalBackwards context f g j equal =
  irrationalForwards context g f j (sym equal)

leanToDashiValue :
  (context : ValueContext) → (j : OddWindow) →
  leanValue context j ≡ dashiValue context j
leanToDashiValue context j =
  trans (leanToBishop context j) (bishopToDashi context j)

OddIrrationalWitness :
  (context : ValueContext) → (OddWindow → Value context) → Set
OddIrrationalWitness context f =
  Σ OddWindow (λ j → IrrationalAt context f j)

leanToBishopIrrationalWitness :
  (context : ValueContext) →
  OddIrrationalWitness context (leanValue context) →
  OddIrrationalWitness context (bishopValue context)
leanToBishopIrrationalWitness context (j , irrational) =
  j , irrationalForwards context
        (leanValue context) (bishopValue context)
        j (leanToBishop context j) irrational

bishopToDashiIrrationalWitness :
  (context : ValueContext) →
  OddIrrationalWitness context (bishopValue context) →
  OddIrrationalWitness context (dashiValue context)
bishopToDashiIrrationalWitness context (j , irrational) =
  j , irrationalForwards context
        (bishopValue context) (dashiValue context)
        j (bishopToDashi context j) irrational

leanToDashiIrrationalWitnessDirect :
  (context : ValueContext) →
  OddIrrationalWitness context (leanValue context) →
  OddIrrationalWitness context (dashiValue context)
leanToDashiIrrationalWitnessDirect context (j , irrational) =
  j , irrationalForwards context
        (leanValue context) (dashiValue context)
        j (leanToDashiValue context j) irrational

leanToDashiIrrationalWitnessViaBishop :
  (context : ValueContext) →
  OddIrrationalWitness context (leanValue context) →
  OddIrrationalWitness context (dashiValue context)
leanToDashiIrrationalWitnessViaBishop context witness =
  bishopToDashiIrrationalWitness context
    (leanToBishopIrrationalWitness context witness)

commutingSquarePreservesWitnessIndex :
  (context : ValueContext) →
  (witness : OddIrrationalWitness context (leanValue context)) →
  fst (leanToDashiIrrationalWitnessDirect context witness) ≡
  fst (leanToDashiIrrationalWitnessViaBishop context witness)
commutingSquarePreservesWitnessIndex context (j , irrational) = refl
