module DASHI.Foundations.InvolutiveTernaryDynamics where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)

import DASHI.Algebra.Trit as Trit

------------------------------------------------------------------------
-- Primitive ternary carrier and derived binary quotient.
--
-- This module deliberately reuses DASHI.Algebra.Trit.  It adds the generic
-- dynamical contracts discussed in the wider DASHI programme without
-- promoting any application-specific physical, economic, biological, or
-- compression claim.

Ternary : Set
Ternary = Trit.Trit

negT : Ternary
negT = Trit.neg

zeroT : Ternary
zeroT = Trit.zer

posT : Ternary
posT = Trit.pos

ιT : Ternary → Ternary
ιT = Trit.inv

ιT-involutive : ∀ t → ιT (ιT t) ≡ t
ιT-involutive = Trit.inv-invol

support : Ternary → Bool
support Trit.neg = true
support Trit.zer = false
support Trit.pos = true

support-invariant : ∀ t → support (ιT t) ≡ support t
support-invariant Trit.neg = refl
support-invariant Trit.zer = refl
support-invariant Trit.pos = refl

zero-fixed : ιT zeroT ≡ zeroT
zero-fixed = refl

------------------------------------------------------------------------
-- Generic involutive carriers.

record InvolutiveCarrier : Set₁ where
  field
    Carrier : Set
    ι : Carrier → Carrier
    ι-involutive : ∀ x → ι (ι x) ≡ x

open InvolutiveCarrier public

ternaryInvolutiveCarrier : InvolutiveCarrier
ternaryInvolutiveCarrier = record
  { Carrier = Ternary
  ; ι = ιT
  ; ι-involutive = ιT-involutive
  }

------------------------------------------------------------------------
-- Involutive controlled dynamics.

record InvolutiveDynamics : Set₁ where
  field
    State : Set
    Control : Set

    stateι : State → State
    controlι : Control → Control

    stateι-involutive : ∀ s → stateι (stateι s) ≡ s
    controlι-involutive : ∀ u → controlι (controlι u) ≡ u

    step : State → Control → State

    step-equivariant :
      ∀ s u →
      step (stateι s) (controlι u) ≡ stateι (step s u)

open InvolutiveDynamics public

------------------------------------------------------------------------
-- Structural predicates derived from a dynamics.

FixedPoint : (D : InvolutiveDynamics) → State D → Set
FixedPoint D e = Σ (Control D) (λ u → step D e u ≡ e)

Invariant :
  (D : InvolutiveDynamics) →
  (Y : Set) →
  (State D → Y) →
  Set
Invariant D Y J = ∀ s u → J (step D s u) ≡ J s

EvenObservable :
  (D : InvolutiveDynamics) →
  (Y : Set) →
  (State D → Y) →
  Set
EvenObservable D Y J = ∀ s → J (stateι D s) ≡ J s

record OddObservable (D : InvolutiveDynamics) : Set₁ where
  field
    Value : Set
    valueι : Value → Value
    observe : State D → Value
    observe-odd : ∀ s → observe (stateι D s) ≡ valueι (observe s)

open OddObservable public

------------------------------------------------------------------------
-- Even action and neutral baseline.
--
-- Nat-valued action is intentionally modest.  The framework can later be
-- instantiated with richer ordered semirings, but this carrier is enough to
-- state symmetry cost, neutral minima, and Lyapunov-style monotonicity without
-- adding postulates.

record EvenAction (D : InvolutiveDynamics) : Set₁ where
  field
    action : State D → Nat
    action-even : ∀ s → action (stateι D s) ≡ action s

    neutral : State D
    neutral-fixed-by-involution : stateι D neutral ≡ neutral
    neutral-minimal : ∀ s → action neutral ≤ action s

open EvenAction public

MonotoneAction :
  (D : InvolutiveDynamics) →
  EvenAction D →
  Set
MonotoneAction D A =
  ∀ s u → action A (step D s u) ≤ action A s

------------------------------------------------------------------------
-- Generability-first trajectory fragments.

record Transition (D : InvolutiveDynamics) : Set where
  constructor transition
  field
    source : State D
    control : Control D
    target : State D
    generated : target ≡ step D source control

open Transition public

mirrorTransition :
  (D : InvolutiveDynamics) →
  Transition D →
  Transition D
mirrorTransition D tr =
  transition
    (stateι D (source tr))
    (controlι D (control tr))
    (stateι D (target tr))
    mirror-generated
  where
    mirror-generated :
      stateι D (target tr) ≡
      step D (stateι D (source tr)) (controlι D (control tr))
    mirror-generated rewrite generated tr | step-equivariant D (source tr) (control tr) = refl

------------------------------------------------------------------------
-- Endogenous admissible controls and derived branching witnesses.

record AdmissibleControls (D : InvolutiveDynamics) : Set₁ where
  field
    Admissible : State D → Control D → Set

    admissible-mirror :
      ∀ s u →
      Admissible s u →
      Admissible (stateι D s) (controlι D u)

open AdmissibleControls public

record BranchWitness
  (D : InvolutiveDynamics)
  (A : AdmissibleControls D)
  (s : State D) : Set where
  constructor branch
  field
    chosenControl : Control D
    chosenIsAdmissible : Admissible A s chosenControl

open BranchWitness public

------------------------------------------------------------------------
-- Non-promotion boundary.

record InvolutiveTernaryDynamicsBoundary : Set where
  constructor boundary
  field
    ternaryCarrierReused : Bool
    binaryIsDerivedSupport : Bool
    applicationAuthorityPromoted : Bool
    compressionTheoremPromoted : Bool
    physicalLawDerived : Bool

canonicalBoundary : InvolutiveTernaryDynamicsBoundary
canonicalBoundary = boundary true true false false false
