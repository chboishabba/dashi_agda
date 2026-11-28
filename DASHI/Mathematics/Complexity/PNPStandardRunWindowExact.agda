module DASHI.Mathematics.Complexity.PNPStandardRunWindowExact where

-- S1: a real arbitrary standard-machine run, not our SAT solver's trace.
-- A radius-k initial tape agreement suffices to replay k actual steps.
-- This is an input-locality necessity, not a superpolynomial lower bound.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong₂; trans; sym)
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as L
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as M
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as R

-- Finite prefix agreement, including simultaneous end-of-list.
-- We do not equate a literal blank cell with a missing cell here.
data Prefix {A : Set} : Nat → List A → List A → Set where
  zeroPrefix : ∀ {as bs} → Prefix zero as bs
  nilPrefix : ∀ {k} → Prefix (suc k) [] []
  consPrefix : ∀ {k a as bs} → Prefix k as bs →
    Prefix (suc k) (a ∷ as) (a ∷ bs)

weaken : ∀ {A : Set} {k} {as bs : List A} →
  Prefix (suc k) as bs → Prefix k as bs
weaken {k = zero} p = zeroPrefix
weaken {k = suc k} nilPrefix = nilPrefix
weaken {k = suc k} (consPrefix p) = consPrefix (weaken p)

push : ∀ {A : Set} {k} {a : A} {as bs} →
  Prefix (suc k) as bs → Prefix k (a ∷ as) (a ∷ bs)
push {k = zero} p = zeroPrefix
push {k = suc k} p = consPrefix (weaken (weaken p))

record Window {State Symbol : Set}
    {machine : M.StandardSingleTapeMachine State Symbol}
    (k : Nat) (a b : M.StandardConfiguration machine) : Set where
  constructor window
  field
    stateEq : M.state a ≡ M.state b
    scanEq : M.scanned a ≡ M.scanned b
    leftEq : Prefix k (M.left a) (M.left b)
    rightEq : Prefix k (M.right a) (M.right b)
open Window

applyWindow : ∀ {State Symbol : Set}
  {machine : M.StandardSingleTapeMachine State Symbol}
  {k} {a b : M.StandardConfiguration machine} →
  Window (suc k) a b → (tr : M.StandardTransition State Symbol) →
  Window k (M.standardApplyTransition machine a tr)
           (M.standardApplyTransition machine b tr)
applyWindow {a = M.standard-configuration [] q c rs}
            {b = M.standard-configuration [] .q .c ss}
    (window refl refl nilPrefix rp)
    (M.standard-transition q' v L.moveLeft) =
  window refl refl (weaken nilPrefix) (push rp)
applyWindow {a = M.standard-configuration (l ∷ ls) q c rs}
            {b = M.standard-configuration (.l ∷ ms) .q .c ss}
    (window refl refl (consPrefix lp) rp)
    (M.standard-transition q' v L.moveLeft) =
  window refl refl lp (push rp)
applyWindow {a = M.standard-configuration ls q c []}
            {b = M.standard-configuration ms .q .c []}
    (window refl refl lp nilPrefix)
    (M.standard-transition q' v L.moveRight) =
  window refl refl (push lp) (weaken nilPrefix)
applyWindow {a = M.standard-configuration ls q c (r ∷ rs)}
            {b = M.standard-configuration ms .q .c (.r ∷ ss)}
    (window refl refl lp (consPrefix rp))
    (M.standard-transition q' v L.moveRight) =
  window refl refl (push lp) rp
applyWindow {a = M.standard-configuration ls q c rs}
            {b = M.standard-configuration ms .q .c ss}
    (window refl refl lp rp)
    (M.standard-transition q' v L.stayPut) =
  window refl refl (weaken lp) (weaken rp)

nextWithRule : ∀ {State Symbol : Set}
  {machine : M.StandardSingleTapeMachine State Symbol}
  (a : M.StandardConfiguration machine) (tr : M.StandardTransition State Symbol) →
  M.transition machine (M.state a) (M.scanned a) ≡ just tr →
  M.standardNext machine a ≡ just (M.standardApplyTransition machine a tr)
nextWithRule a tr selected rewrite selected = refl

nothingNotJust : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
nothingNotJust ()

justInjective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
justInjective refl = refl

replayStep : ∀ {State Symbol : Set}
  {machine : M.StandardSingleTapeMachine State Symbol}
  {k} {a a' b : M.StandardConfiguration machine} →
  Window (suc k) a b → M.standardNext machine a ≡ just a' →
  Σ (M.StandardConfiguration machine) (λ b' →
    (M.standardNext machine b ≡ just b') × Window k a' b')
replayStep {machine = machine} {a = a} {b = b} W edge
  with M.transition machine (M.state a) (M.scanned a) in selected
... | nothing with edge
...   | ()
replayStep {machine = machine} {a = a} {b = b} W edge
    | just tr with edge
...   | refl =
  M.standardApplyTransition machine b tr ,
  nextWithRule b tr
    (trans (cong₂ (M.transition machine) (sym (stateEq W)) (sym (scanEq W)))
      selected) ,
  applyWindow W tr

replayRun : ∀ {State Symbol : Set}
  {machine : M.StandardSingleTapeMachine State Symbol}
  {k} {a b finish : M.StandardConfiguration machine} →
  Window k a b → R.StandardExactRun machine k a finish →
  Σ (M.StandardConfiguration machine) (λ finish' →
    R.StandardExactRun machine k b finish' × (M.state finish ≡ M.state finish'))
replayRun {b = b} W R.standardRunDone = b , R.standardRunDone , stateEq W
replayRun W (R.standardRunStep edge rest) with replayStep W edge
... | b' , edge' , W' with replayRun W' rest
...   | finish' , run' , same =
  finish' , R.standardRunStep edge' run' , same

-- Consequence: every actual k-step run of any deterministic single-tape
-- machine induces the same control decision on this whole input cylinder.
-- A consumer-changing collision inside it rules out that k-step decision.
-- The full visited-coordinate refinement, same-run sharing charge and
-- superpolynomial exclusion are separate obligations.
