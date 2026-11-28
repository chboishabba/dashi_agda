module DASHI.Mathematics.Complexity.PNPStandardRunAsymmetricWindowExact where

-- Refine the existing symmetric run window to the actual path-dependent
-- left/right input cylinder. This is not a semantic time lower bound.
-- Source-written; native kernel pending.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong₂; trans; sym)
import DASHI.Mathematics.Complexity.PNPStandardRunWindowExact as W
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as L
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as M
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as R

pred : Nat → Nat
pred zero = zero
pred (suc n) = n

emptyPrefix : ∀ {A : Set} k → W.Prefix {A} k [] []
emptyPrefix zero = W.zeroPrefix
emptyPrefix (suc k) = W.nilPrefix

prepend : ∀ {A : Set} k {a : A} {as bs} →
  W.Prefix (pred k) as bs → W.Prefix k (a ∷ as) (a ∷ bs)
prepend zero p = W.zeroPrefix
prepend (suc k) p = W.consPrefix p

needL needR : L.Direction → Nat → Nat
needL L.moveLeft k = suc k
needL L.moveRight k = pred k
needL L.stayPut k = k
needR L.moveLeft k = pred k
needR L.moveRight k = suc k
needR L.stayPut k = k

module On {State Symbol : Set} (machine : M.StandardSingleTapeMachine State Symbol) where
  Config = M.StandardConfiguration machine

  record Window (l r : Nat) (a b : Config) : Set where
    constructor window
    field
      stateEq : M.state a ≡ M.state b
      scanEq : M.scanned a ≡ M.scanned b
      leftEq : W.Prefix l (M.left a) (M.left b)
      rightEq : W.Prefix r (M.right a) (M.right b)
  open Window

  applyWindow : ∀ {l r} {a b : Config} (tr : M.StandardTransition State Symbol) →
    Window (needL (M.direction tr) l) (needR (M.direction tr) r) a b →
    Window l r (M.standardApplyTransition machine a tr)
               (M.standardApplyTransition machine b tr)
  applyWindow {l} {r} {a = M.standard-configuration [] q c rs}
    {b = M.standard-configuration [] .q .c ss}
    (M.standard-transition q' v L.moveLeft) (window refl refl W.nilPrefix rp) =
    window refl refl (emptyPrefix l) (prepend r rp)
  applyWindow {l} {r} {a = M.standard-configuration (u ∷ us) q c rs}
    {b = M.standard-configuration (.u ∷ vs) .q .c ss}
    (M.standard-transition q' v L.moveLeft) (window refl refl (W.consPrefix lp) rp) =
    window refl refl lp (prepend r rp)
  applyWindow {l} {r} {a = M.standard-configuration ls q c []}
    {b = M.standard-configuration ms .q .c []}
    (M.standard-transition q' v L.moveRight) (window refl refl lp W.nilPrefix) =
    window refl refl (prepend l lp) (emptyPrefix r)
  applyWindow {l} {r} {a = M.standard-configuration ls q c (u ∷ us)}
    {b = M.standard-configuration ms .q .c (.u ∷ vs)}
    (M.standard-transition q' v L.moveRight) (window refl refl lp (W.consPrefix rp)) =
    window refl refl (prepend l lp) rp
  applyWindow {a = M.standard-configuration ls q c rs}
    {b = M.standard-configuration ms .q .c ss}
    (M.standard-transition q' v L.stayPut) (window refl refl lp rp) =
    window refl refl lp rp

  -- Requirements are derived BACKWARDS from the actual run relation.
  -- The final scanned symbol is retained too, so the cylinder is sufficient,
  -- not claimed minimal for a control-only decision.
  record Requirement {k a finish} (run : R.StandardExactRun machine k a finish) : Set where
    field
      leftNeed rightNeed : Nat
      replay : ∀ b → Window leftNeed rightNeed a b →
        Σ Config (λ out → R.StandardExactRun machine k b out × (M.state finish ≡ M.state out))
  open Requirement

  derive : ∀ {k a finish} (run : R.StandardExactRun machine k a finish) → Requirement run
  derive R.standardRunDone = record
    { leftNeed = zero ; rightNeed = zero
    ; replay = λ b w → b , R.standardRunDone , stateEq w }
  derive {a = a} (R.standardRunStep edge rest)
    with M.transition machine (M.state a) (M.scanned a) in eq
  ... | nothing with edge
  ...   | ()
  derive {a = a} {finish = finish} (R.standardRunStep edge rest) | just tr with edge
  ... | refl = record
    { leftNeed = needL (M.direction tr) (leftNeed rec)
    ; rightNeed = needR (M.direction tr) (rightNeed rec)
    ; replay = λ b w → extend b w }
    where
      rec = derive rest
      extend : ∀ b → Window (needL (M.direction tr) (leftNeed rec))
        (needR (M.direction tr) (rightNeed rec)) a b →
        Σ Config (λ out → R.StandardExactRun machine _ b out × (M.state finish ≡ M.state out))
      extend b w with replay rec (M.standardApplyTransition machine b tr) (applyWindow tr w)
      ... | out , rr , same = out ,
        R.standardRunStep
          (W.nextWithRule b tr
            (trans (cong₂ (M.transition machine) (sym (stateEq w)) (sym (scanEq w))) eq))
          rr , same
