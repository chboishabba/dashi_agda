module DASHI.Foundations.FiniteInvolutiveTrajectory where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)

import DASHI.Foundations.InvolutiveTernaryDynamics as ITD

data FinitePath (D : ITD.InvolutiveDynamics) :
  Nat → ITD.State D → ITD.State D → Set where
  stop : ∀ {s} → FinitePath D zero s s
  advance : ∀ {n s z} (u : ITD.Control D) →
    FinitePath D n (ITD.step D s u) z →
    FinitePath D (suc n) s z

FiniteOrbit : (D : ITD.InvolutiveDynamics) → Nat → ITD.State D → Set
FiniteOrbit D n s = FinitePath D n s s

pathLength : ∀ {D n s z} → FinitePath D n s z → Nat
pathLength {n = n} _ = n

mirrorPath : ∀ {D n s z} →
  FinitePath D n s z →
  FinitePath D n (ITD.stateι D s) (ITD.stateι D z)
mirrorPath {D} stop = stop
mirrorPath {D} (advance u p) rewrite ITD.step-equivariant D _ u =
  advance (ITD.controlι D u) (mirrorPath p)

pathAction : ∀ {D n s z} →
  ITD.EvenAction D → FinitePath D n s z → Nat
pathAction A {s = s} stop = ITD.action A s
pathAction A {s = s} (advance u p) =
  ITD.action A s + pathAction A p

record LowActionOrbit
  (D : ITD.InvolutiveDynamics)
  (A : ITD.EvenAction D)
  (n : Nat)
  (s : ITD.State D) : Set where
  constructor lowActionOrbit
  field
    orbitPath : FiniteOrbit D n s
    actionBudget : Nat
    actionWithinBudget : pathAction A orbitPath ≡ actionBudget

open LowActionOrbit public

fixedPoint→orbit1 : ∀ {D s} → ITD.FixedPoint D s → FiniteOrbit D (suc zero) s
fixedPoint→orbit1 (u , eq) rewrite eq = advance u stop
