module DASHI.Mathematics.Complexity.PNPDAGLiveCompilerExact where

-- Reuse the actual indexed program, backward dependency proof and
-- restriction compiler. Drop an undemanded gate without emitting it.
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as N
import Data.Fin.Properties as F
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as C
import DASHI.Mathematics.Complexity.PNPDAGSparseDependencyExact as S
import DASHI.Mathematics.Complexity.PNPDAGRestrictionCompilerExact as R

wireDec : ∀ {n g} (u v : C.WireRef n g) → Dec (u ≡ v)
wireDec (C.inputWire i) (C.inputWire j) with i F.≟ j
... | yes refl = yes refl
... | no ne = no (λ { refl → ne refl })
wireDec (C.inputWire i) (C.gateWire j) = no (λ ())
wireDec (C.gateWire i) (C.inputWire j) = no (λ ())
wireDec (C.gateWire i) (C.gateWire j) with i F.≟ j
... | yes refl = yes refl
... | no ne = no (λ { refl → ne refl })

sumDec : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
sumDec (yes a) b = yes (inj₁ a)
sumDec (no na) (yes b) = yes (inj₂ b)
sumDec (no na) (no nb) = no (λ { (inj₁ a) → na a ; (inj₂ b) → nb b })

pairDec : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
pairDec (yes a) (yes b) = yes (a , b)
pairDec (no na) b = no (λ { (a , _) → na a })
pairDec (yes a) (no nb) = no (λ { (_ , b) → nb b })

readsDec : ∀ {n g} (a : C.Gate n g) (w : C.WireRef n g) → Dec (S.Reads a w)
readsDec (C.constantGate b) w = no (λ x → x)
readsDec (C.notGate u) w = wireDec w u
readsDec (C.andGate u v) w = sumDec (wireDec w u) (wireDec w v)
readsDec (C.orGate u v) w = sumDec (wireDec w u) (wireDec w v)

decPre : ∀ {n g} (a : C.Gate n g) (D : S.Demand n (suc g)) →
  (∀ w → Dec (D w)) → ∀ w → Dec (S.pre a D w)
decPre a D dec w = sumDec (dec (S.lift w))
  (pairDec (dec (C.gateWire fzero)) (readsDec a w))

planLive : ∀ {n g h} (im : C.WireRef n g → R.Image n h)
  (a : C.Gate n g) (x : Vec Bool n) (v : Vec Bool g) (u : Vec Bool h) →
  (∀ w → S.Reads a w → R.observe (im w) x u ≡ C.evaluateWire w x v) →
  R.evalPlan (R.planGate im a) x u ≡ C.evaluateGate a x v
planLive im (C.constantGate b) x v u eq = refl
planLive im (C.notGate w) x v u eq =
  trans (R.notExact (im w) x u) (cong Cook.notBool (eq w refl))
planLive im (C.andGate w z) x v u eq =
  trans (R.andExact (im w) (im z) x u)
    (cong₂ Cook.andBool (eq w (inj₁ refl)) (eq z (inj₂ refl)))
planLive im (C.orGate w z) x v u eq =
  trans (R.orExact (im w) (im z) x u)
    (cong₂ Cook.orBool (eq w (inj₁ refl)) (eq z (inj₂ refl)))

record Compiled {n g : Nat} (p : C.GateProgram n g) (D : S.Demand n g) : Set where
  field
    count : Nat
    program : C.GateProgram n count
    image : C.WireRef n g → R.Image n count
    bound : count ≤ g
    exact : ∀ x w → D w → R.observe (image w) x (C.evaluateProgram program x) ≡
      C.evaluateWire w x (C.evaluateProgram p x)
open Compiled

compile : ∀ {n g} (p : C.GateProgram n g) (D : S.Demand n g) →
  (∀ w → Dec (D w)) → Compiled p D
compile C.noGates D dec = record
  { count = zero ; program = C.noGates
  ; image = λ { (C.inputWire i) → R.wire (C.inputWire i) ; (C.gateWire ()) }
  ; bound = z≤n
  ; exact = λ { x (C.inputWire i) h → refl ; x (C.gateWire ()) } }
compile (C.appendGate p a) D dec with compile p (S.pre a D) (decPre a D dec)
... | old with dec (C.gateWire fzero)
...   | no dead = record
  { count = count old ; program = program old
  ; image = R.extendAlias (image old) (R.known false)
  ; bound = N.≤-step (bound old)
  ; exact = λ
    { x (C.inputWire i) h → exact old x (C.inputWire i) (inj₁ h)
    ; x (C.gateWire (fsuc i)) h → exact old x (C.gateWire i) (inj₁ h)
    ; x (C.gateWire fzero) h → ⊥-elim (dead h) } }
...   | yes live with R.planGate (image old) a in eq
...     | R.alias v = record
  { count = count old ; program = program old ; image = R.extendAlias (image old) v
  ; bound = N.≤-step (bound old)
  ; exact = λ
    { x (C.inputWire i) h → exact old x (C.inputWire i) (inj₁ h)
    ; x (C.gateWire (fsuc i)) h → exact old x (C.gateWire i) (inj₁ h)
    ; x (C.gateWire fzero) h →
        trans (cong (λ z → R.evalPlan z x (C.evaluateProgram (program old) x)) (sym eq))
          (planLive (image old) a x (C.evaluateProgram p x)
            (C.evaluateProgram (program old) x) (λ w read → exact old x w (inj₂ (live , read)))) } }
...     | R.fresh b = record
  { count = suc (count old) ; program = C.appendGate (program old) b
  ; image = R.extendFresh (image old) ; bound = s≤s (bound old)
  ; exact = λ
    { x (C.inputWire i) h →
        trans (R.weakenExact (image old (C.inputWire i)) x (C.evaluateProgram (program old) x) _)
          (exact old x (C.inputWire i) (inj₁ h))
    ; x (C.gateWire (fsuc i)) h →
        trans (R.weakenExact (image old (C.gateWire i)) x (C.evaluateProgram (program old) x) _)
          (exact old x (C.gateWire i) (inj₁ h))
    ; x (C.gateWire fzero) h →
        trans (cong (λ z → R.evalPlan z x (C.evaluateProgram (program old) x)) (sym eq))
          (planLive (image old) a x (C.evaluateProgram p x)
            (C.evaluateProgram (program old) x) (λ w read → exact old x w (inj₂ (live , read)))) } }

prune : ∀ {n} → C.ConcreteBooleanCircuit n → C.ConcreteBooleanCircuit n
prune c =
  let t = compile (C.program c) (λ w → w ≡ C.outputWire c)
        (λ w → wireDec w (C.outputWire c))
  in R.finish (program t) (image t (C.outputWire c))

pruneExact : ∀ {n} (c : C.ConcreteBooleanCircuit n) (x : Vec Bool n) →
  C.evaluateCircuit (prune c) x ≡ C.evaluateCircuit c x
pruneExact c x =
  let t = compile (C.program c) (λ w → w ≡ C.outputWire c)
        (λ w → wireDec w (C.outputWire c))
  in trans (R.finishExact (program t) (image t (C.outputWire c)) x)
    (exact t x (C.outputWire c) refl)

pruneBound : ∀ {n} (c : C.ConcreteBooleanCircuit n) →
  C.circuitSize (prune c) ≤ suc (C.circuitSize c)
pruneBound c =
  let t = compile (C.program c) (λ w → w ≡ C.outputWire c)
        (λ w → wireDec w (C.outputWire c))
  in R.finishBound (program t) (image t (C.outputWire c)) (bound t)

-- Target program is materialized and indexed. This source-level
-- decision procedure may revisit demand predicates, so its own
-- polynomial compilation-time bound is NOT asserted. Gate count
-- and construction time are different. Native kernel pending.
