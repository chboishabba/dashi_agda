module Verification.JacobianNoninjectiveRegression where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

-- Public attribution
-- ------------------
-- This concrete polynomial map was publicly announced by Levent Alpöge on
-- 20 July 2026.  His announcement credited Akhil Mathew for asking about the
-- problem and Fable for producing the example.  DASHI attributes the public
-- mathematical announcement to Alpöge and does not claim discovery priority.
--
-- Exact polynomial expansion and rational witness evaluation are executed by
-- scripts/check_jacobian_noninjective_example.py.  The small logical theorem
-- below is kernel-checked: two unequal inputs with equal outputs refute
-- injectivity.  The polynomial-ring computation itself remains an executable
-- exact-arithmetic receipt rather than an Agda-normalised polynomial proof.

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

Injective : ∀ {A B : Set} → (A → B) → Set
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

record NonInjectiveWitness {A B : Set} (f : A → B) : Set where
  constructor nonInjectiveWitness
  field
    left right : A
    distinct   : ¬ (left ≡ right)
    collision  : f left ≡ f right

witnessRefutesInjectivity :
  ∀ {A B : Set} {f : A → B} →
  NonInjectiveWitness f →
  ¬ Injective f
witnessRefutesInjectivity w injective =
  NonInjectiveWitness.distinct w
    (injective (NonInjectiveWitness.collision w))

record ExactJacobianCounterexampleReceipt : Set where
  constructor receipt
  field
    publicAnnouncer                : String
    announcementDate              : String
    creditedQuestioner            : String
    creditedSystem                : String
    ambientDimension              : Nat
    determinantConstant           : String
    determinantIdentityOK         : Bool
    distinctWitnessCount          : Nat
    commonImage                   : String
    fibreWitnessesOK              : Bool
    noninjectivityImplicationProved : Bool
    polynomialIdentityKernelProved  : Bool
    generalDimensionThreeRefuted    : Bool
    dimensionTwoAffected            : Bool

alpogeJacobianCounterexampleReceipt : ExactJacobianCounterexampleReceipt
alpogeJacobianCounterexampleReceipt =
  receipt
    "Levent Alpöge"
    "2026-07-20"
    "Akhil Mathew"
    "Fable"
    3
    "-2"
    true
    3
    "(-1/4,0,0)"
    true
    true
    false
    true
    false

-- Interpretation boundary
-- -----------------------
-- The checked exact computation establishes a constant nonzero Jacobian and a
-- three-point fibre for the displayed polynomial map.  Together with the
-- kernel theorem witnessRefutesInjectivity, this is a counterexample to the
-- general Jacobian conjecture in dimension 3.  Adding untouched coordinates
-- transports the counterexample to every dimension n ≥ 3.  Nothing in this
-- receipt settles the dimension-2 case, and nothing here changes unrelated
-- analytic, physical, or empirical DASHI claims.