module DASHI.Mathematics.Complexity.PNPDAGSparseDependencyExact where

-- Backwards liveness on the existing indexed gate/suffix. Demand is a
-- set of wire references (predicate), not a duplicated expression tree.
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec.Base using (Vec; _∷_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as C
import DASHI.Mathematics.Complexity.PNPDAGCutsetFactorizationExact as Cut

lift : ∀ {n g} → C.WireRef n g → C.WireRef n (suc g)
lift (C.inputWire i) = C.inputWire i
lift (C.gateWire i) = C.gateWire (fsuc i)

Reads : ∀ {n g} → C.Gate n g → C.WireRef n g → Set
Reads (C.constantGate b) w = ⊥
Reads (C.notGate u) w = w ≡ u
Reads (C.andGate u v) w = (w ≡ u) ⊎ (w ≡ v)
Reads (C.orGate u v) w = (w ≡ u) ⊎ (w ≡ v)

Demand : Nat → Nat → Set₁
Demand n g = C.WireRef n g → Set

Agree : ∀ {n g} → Demand n g → Vec Bool n → Vec Bool g →
  Vec Bool n → Vec Bool g → Set
Agree D x v y u = ∀ w → D w → C.evaluateWire w x v ≡ C.evaluateWire w y u

gateAgree : ∀ {n g} (a : C.Gate n g) {x y : Vec Bool n} {v u : Vec Bool g} →
  Agree (Reads a) x v y u → C.evaluateGate a x v ≡ C.evaluateGate a y u
gateAgree (C.constantGate b) h = refl
gateAgree (C.notGate w) h = cong Cook.notBool (h w refl)
gateAgree (C.andGate w z) h = cong₂ Cook.andBool (h w (inj₁ refl)) (h z (inj₂ refl))
gateAgree (C.orGate w z) h = cong₂ Cook.orBool (h w (inj₁ refl)) (h z (inj₂ refl))

pre : ∀ {n g} → C.Gate n g → Demand n (suc g) → Demand n g
pre a D w = D (lift w) ⊎ (D (C.gateWire fzero) × Reads a w)

stepAgree : ∀ {n g} (a : C.Gate n g) (D : Demand n (suc g))
  {x y : Vec Bool n} {v u : Vec Bool g} →
  Agree (pre a D) x v y u →
  Agree D x (C.evaluateGate a x v ∷ v) y (C.evaluateGate a y u ∷ u)
stepAgree a D h (C.inputWire i) d = h (C.inputWire i) (inj₁ d)
stepAgree a D h (C.gateWire (fsuc i)) d = h (C.gateWire i) (inj₁ d)
stepAgree a D h (C.gateWire fzero) d = gateAgree a (λ w r → h w (inj₂ (d , r)))

need : ∀ {n g h} → Cut.Suffix n g h → Demand n h → Demand n g
need Cut.stop D = D
need (Cut.next s a) D = need s (pre a D)

needAgree : ∀ {n g h} (s : Cut.Suffix n g h) (D : Demand n h)
  {x y : Vec Bool n} {v u : Vec Bool g} →
  Agree (need s D) x v y u →
  Agree D x (Cut.evalFrom s x v) y (Cut.evalFrom s y u)
needAgree Cut.stop D h = h
needAgree (Cut.next s a) D h = stepAgree a D (needAgree s (pre a D) h)

outputNeed : ∀ {n g h} → Cut.Suffix n g h → C.WireRef n h → Demand n g
outputNeed s w = need s (λ z → z ≡ w)

sparseOutputExact : ∀ {n g h} (p : C.GateProgram n g) (s : Cut.Suffix n g h)
  (w : C.WireRef n h) (x y : Vec Bool n) →
  Agree (outputNeed s w) x (C.evaluateProgram p x) y (C.evaluateProgram p y) →
  C.evaluateWire w x (C.evaluateProgram (Cut.attach p s) x) ≡
  C.evaluateWire w y (C.evaluateProgram (Cut.attach p s) y)
sparseOutputExact p s w x y h =
  trans (Cut.outputFactor p s w x)
    (trans (needAgree s (λ z → z ≡ w) h w refl)
      (sym (Cut.outputFactor p s w y)))

-- The original prefix and suffix are preserved, and irrelevant old
-- wires need not agree. The demand predicate may be implemented by a
-- finite deduplicated backwards scan; no arbitrary combiner or rank.
-- Sparse materialized renumbering and its exact machine cost are
-- separate from this native semantic proof.
