module DASHI.Mathematics.Complexity.PNPStandardTwoPhaseRunExact where

-- Actual standardNext / StandardExactRun attachment. This semantic
-- two-stage machine is independent of the source execution trace.
-- The separate finite-window prime-tag compiler realizes its local
-- read/write stages; finite-presentation serialization and full
-- physical clock are NOT discharged by this semantic run transport.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as S
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as R

twice : Nat → Nat
twice zero = zero
twice (suc n) = suc (suc (twice n))

module Stage {State Symbol : Set}
    (machine : S.StandardSingleTapeMachine State Symbol) where

  Config : Set
  Config = S.StandardConfiguration machine
  Transition : Set
  Transition = S.StandardTransition State Symbol

  data Phase : Set where
    boundary : Config → Phase
    prepared : Config → Transition → Phase

  next : Phase → Maybe Phase
  next (boundary c) with S.transition machine (S.state c) (S.scanned c)
  ... | nothing = nothing
  ... | just t = just (prepared c t)
  next (prepared c t) = just (boundary (S.standardApplyTransition machine c t))

  data ExactRun : Nat → Phase → Phase → Set where
    done : ∀ {c} → ExactRun zero c c
    edge : ∀ {n c d e} → next c ≡ just d →
      ExactRun n d e → ExactRun (suc n) c e

  sourceHalt : ∀ {c} → S.standardNext machine c ≡ nothing →
    next (boundary c) ≡ nothing
  sourceHalt {c} h with S.transition machine (S.state c) (S.scanned c)
  ... | nothing = refl
  ... | just t with h
  ...   | ()

  liftEdge : ∀ {c d} → S.standardNext machine c ≡ just d →
    ExactRun (suc (suc zero)) (boundary c) (boundary d)
  liftEdge {c} h with S.transition machine (S.state c) (S.scanned c)
  ... | nothing with h
  ...   | ()
  liftEdge {c} h | just t with h
  ...   | refl = edge refl (edge refl done)

  lift : ∀ {n c d} → R.StandardExactRun machine n c d →
    ExactRun (twice n) (boundary c) (boundary d)
  lift R.standardRunDone = done
  lift (R.standardRunStep h p) with liftEdge h
  ... | edge h1 (edge h2 done) = edge h1 (edge h2 (lift p))
