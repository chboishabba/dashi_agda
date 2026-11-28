module DASHI.Mathematics.Complexity.PNPDAGCachedDemandExact where

-- Explicit finite mask specification over the original newest-first
-- indexed DAG. Each reverse step consumes one gate and marks its at
-- most two operands. Vector access is NOT claimed constant time.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Nat.Base using (_≤_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as C
import DASHI.Mathematics.Complexity.PNPDAGSparseDependencyExact as S
import DASHI.Mathematics.Complexity.PNPDAGLiveCompilerExact as L
import DASHI.Mathematics.Complexity.PNPDAGRestrictionCompilerExact as R

Equiv : Set → Set → Set
Equiv P Q = (P → Q) × (Q → P)

setBit : ∀ {n} → Fin n → Vec Bool n → Vec Bool n
setBit fzero (b ∷ bs) = true ∷ bs
setBit (fsuc i) (b ∷ bs) = b ∷ setBit i bs

setExact : ∀ {n} (i j : Fin n) (v : Vec Bool n) →
  Equiv (C.lookupVec j (setBit i v) ≡ true)
    ((j ≡ i) ⊎ (C.lookupVec j v ≡ true))
setExact fzero fzero (b ∷ bs) = (λ _ → inj₁ refl) , (λ _ → refl)
setExact fzero (fsuc j) (b ∷ bs) = inj₂ , (λ { (inj₁ ()) ; (inj₂ h) → h })
setExact (fsuc i) fzero (b ∷ bs) = inj₂ , (λ { (inj₁ ()) ; (inj₂ h) → h })
setExact (fsuc i) (fsuc j) (b ∷ bs) =
  (λ h → caseForward (proj₁ (setExact i j bs) h)) ,
  (λ h → proj₂ (setExact i j bs) (caseBack h))
  where
  caseForward : (j ≡ i) ⊎ (C.lookupVec j bs ≡ true) →
    (fsuc j ≡ fsuc i) ⊎ (C.lookupVec j bs ≡ true)
  caseForward (inj₁ e) = inj₁ (cong fsuc e)
  caseForward (inj₂ e) = inj₂ e
  caseBack : (fsuc j ≡ fsuc i) ⊎ (C.lookupVec j bs ≡ true) →
    (j ≡ i) ⊎ (C.lookupVec j bs ≡ true)
  caseBack (inj₁ refl) = inj₁ refl
  caseBack (inj₂ e) = inj₂ e

record Mask (n g : Nat) : Set where
  constructor mask
  field
    inputs : Vec Bool n
    gates : Vec Bool g

bit : ∀ {n g} → Mask n g → C.WireRef n g → Bool
bit (mask i v) (C.inputWire j) = C.lookupVec j i
bit (mask i v) (C.gateWire j) = C.lookupVec j v

Truth : ∀ {n g} → Mask n g → S.Demand n g
Truth m w = bit m w ≡ true

mark : ∀ {n g} → C.WireRef n g → Mask n g → Mask n g
mark (C.inputWire j) (mask i v) = mask (setBit j i) v
mark (C.gateWire j) (mask i v) = mask i (setBit j v)

markExact : ∀ {n g} (u w : C.WireRef n g) (m : Mask n g) →
  Equiv (Truth (mark u m) w) ((w ≡ u) ⊎ Truth m w)
markExact (C.inputWire i) (C.inputWire j) (mask x v) =
  (λ h → f (proj₁ (setExact i j x) h)) ,
  (λ h → proj₂ (setExact i j x) (b h))
  where
  f : (j ≡ i) ⊎ (C.lookupVec j x ≡ true) →
    (C.inputWire {gates = _} j ≡ C.inputWire i) ⊎ (C.lookupVec j x ≡ true)
  f (inj₁ e) = inj₁ (cong C.inputWire e)
  f (inj₂ e) = inj₂ e
  b : (C.inputWire {gates = _} j ≡ C.inputWire i) ⊎ (C.lookupVec j x ≡ true) →
    (j ≡ i) ⊎ (C.lookupVec j x ≡ true)
  b (inj₁ refl) = inj₁ refl
  b (inj₂ e) = inj₂ e
markExact (C.inputWire i) (C.gateWire j) (mask x v) =
  inj₂ , (λ { (inj₁ ()) ; (inj₂ h) → h })
markExact (C.gateWire i) (C.inputWire j) (mask x v) =
  inj₂ , (λ { (inj₁ ()) ; (inj₂ h) → h })
markExact (C.gateWire i) (C.gateWire j) (mask x v) =
  (λ h → f (proj₁ (setExact i j v) h)) ,
  (λ h → proj₂ (setExact i j v) (b h))
  where
  f : (j ≡ i) ⊎ (C.lookupVec j v ≡ true) →
    (C.gateWire {inputs = _} j ≡ C.gateWire i) ⊎ (C.lookupVec j v ≡ true)
  f (inj₁ e) = inj₁ (cong C.gateWire e)
  f (inj₂ e) = inj₂ e
  b : (C.gateWire {inputs = _} j ≡ C.gateWire i) ⊎ (C.lookupVec j v ≡ true) →
    (j ≡ i) ⊎ (C.lookupVec j v ≡ true)
  b (inj₁ refl) = inj₁ refl
  b (inj₂ e) = inj₂ e

markTwoExact : ∀ {n g} (u v w : C.WireRef n g) (m : Mask n g) →
  Equiv (Truth (mark u (mark v m)) w) (((w ≡ u) ⊎ (w ≡ v)) ⊎ Truth m w)
markTwoExact u v w m = forward , backward
  where
  forward : Truth (mark u (mark v m)) w → ((w ≡ u) ⊎ (w ≡ v)) ⊎ Truth m w
  forward h with proj₁ (markExact u w (mark v m)) h
  ... | inj₁ e = inj₁ (inj₁ e)
  ... | inj₂ e with proj₁ (markExact v w m) e
  ...   | inj₁ f = inj₁ (inj₂ f)
  ...   | inj₂ f = inj₂ f
  backward : ((w ≡ u) ⊎ (w ≡ v)) ⊎ Truth m w → Truth (mark u (mark v m)) w
  backward (inj₁ (inj₁ e)) = proj₂ (markExact u w (mark v m)) (inj₁ e)
  backward (inj₁ (inj₂ e)) = proj₂ (markExact u w (mark v m)) (inj₂ (proj₂ (markExact v w m) (inj₁ e)))
  backward (inj₂ e) = proj₂ (markExact u w (mark v m)) (inj₂ (proj₂ (markExact v w m) (inj₂ e)))

markReads : ∀ {n g} → C.Gate n g → Mask n g → Mask n g
markReads (C.constantGate b) m = m
markReads (C.notGate u) m = mark u m
markReads (C.andGate u v) m = mark u (mark v m)
markReads (C.orGate u v) m = mark u (mark v m)

readsExact : ∀ {n g} (a : C.Gate n g) (w : C.WireRef n g) (m : Mask n g) →
  Equiv (Truth (markReads a m) w) (S.Reads a w ⊎ Truth m w)
readsExact (C.constantGate b) w m = inj₂ , (λ { (inj₁ ()) ; (inj₂ h) → h })
readsExact (C.notGate u) w m = markExact u w m
readsExact (C.andGate u v) w m = markTwoExact u v w m
readsExact (C.orGate u v) w m = markTwoExact u v w m

advance : ∀ {n g} → C.Gate n g → Mask n (suc g) → Mask n g
advance a (mask x (false ∷ v)) = mask x v
advance a (mask x (true ∷ v)) = markReads a (mask x v)

liftTruth : ∀ {n g} (x : Vec Bool n) (v : Vec Bool g) (b : Bool)
  (w : C.WireRef n g) → Equiv (Truth (mask x v) w) (Truth (mask x (b ∷ v)) (S.lift w))
liftTruth x v b (C.inputWire i) = (λ h → h) , (λ h → h)
liftTruth x v b (C.gateWire i) = (λ h → h) , (λ h → h)

advanceExact : ∀ {n g} (a : C.Gate n g) (m : Mask n (suc g)) (w : C.WireRef n g) →
  Equiv (Truth (advance a m) w) (S.pre a (Truth m) w)
advanceExact a (mask x (false ∷ v)) w =
  (λ h → inj₁ (proj₁ (liftTruth x v false w) h)) ,
  (λ { (inj₁ h) → proj₂ (liftTruth x v false w) h ; (inj₂ (() , r)) })
advanceExact a (mask x (true ∷ v)) w = forward , backward
  where
  forward : Truth (markReads a (mask x v)) w → S.pre a (Truth (mask x (true ∷ v))) w
  forward h with proj₁ (readsExact a w (mask x v)) h
  ... | inj₁ e = inj₂ (refl , e)
  ... | inj₂ e = inj₁ (proj₁ (liftTruth x v true w) e)
  backward : S.pre a (Truth (mask x (true ∷ v))) w → Truth (markReads a (mask x v)) w
  backward (inj₁ h) = proj₂ (readsExact a w (mask x v)) (inj₂ (proj₂ (liftTruth x v true w) h))
  backward (inj₂ (h , r)) = proj₂ (readsExact a w (mask x v)) (inj₁ r)

preTransfer : ∀ {n g} (a : C.Gate n g) (m : Mask n (suc g))
  (D : S.Demand n (suc g)) → (∀ w → Equiv (Truth m w) (D w)) →
  ∀ w → Equiv (Truth (advance a m) w) (S.pre a D w)
preTransfer a m D eq w = forward , backward
  where
  forward : Truth (advance a m) w → S.pre a D w
  forward h with proj₁ (advanceExact a m w) h
  ... | inj₁ e = inj₁ (proj₁ (eq (S.lift w)) e)
  ... | inj₂ (e , r) = inj₂ (proj₁ (eq (C.gateWire fzero)) e , r)
  backward : S.pre a D w → Truth (advance a m) w
  backward (inj₁ h) = proj₂ (advanceExact a m w) (inj₁ (proj₂ (eq (S.lift w)) h))
  backward (inj₂ (h , r)) = proj₂ (advanceExact a m w) (inj₂ (proj₂ (eq (C.gateWire fzero)) h , r))

boolDec : (b : Bool) → Dec (b ≡ true)
boolDec true = yes refl
boolDec false = no (λ ())

transferDec : ∀ {P Q : Set} → Equiv P Q → Dec P → Dec Q
transferDec e (yes h) = yes (proj₁ e h)
transferDec e (no h) = no (λ q → h (proj₂ e q))

schedule : ∀ {n g} (p : C.GateProgram n g) (m : Mask n g) (D : S.Demand n g) →
  (∀ w → Equiv (Truth m w) (D w)) → L.Schedule p D
schedule C.noGates m D eq = L.stop
schedule (C.appendGate p a) m D eq =
  L.next (transferDec (eq (C.gateWire fzero)) (boolDec (bit m (C.gateWire fzero))))
    (schedule p (advance a m) (S.pre a D) (preTransfer a m D eq))

zeros : (n : Nat) → Vec Bool n
zeros zero = []
zeros (suc n) = false ∷ zeros n

zerosFalse : ∀ {n} (i : Fin n) → C.lookupVec i (zeros n) ≡ true → ⊥
zerosFalse fzero ()
zerosFalse (fsuc i) h = zerosFalse i h

emptyFalse : ∀ {n g} (w : C.WireRef n g) → Truth (mask (zeros n) (zeros g)) w → ⊥
emptyFalse (C.inputWire i) = zerosFalse i
emptyFalse (C.gateWire i) = zerosFalse i

outputMask : ∀ {n g} → C.WireRef n g → Mask n g
outputMask {n} {g} w = mark w (mask (zeros n) (zeros g))

outputExact : ∀ {n g} (w u : C.WireRef n g) → Equiv (Truth (outputMask w) u) (u ≡ w)
outputExact {n} {g} w u = forward , backward
  where
  forward : Truth (outputMask w) u → u ≡ w
  forward h with proj₁ (markExact w u (mask (zeros n) (zeros g))) h
  ... | inj₁ e = e
  ... | inj₂ e = ⊥-elim (emptyFalse u e)
  backward : u ≡ w → Truth (outputMask w) u
  backward h = proj₂ (markExact w u (mask (zeros n) (zeros g))) (inj₁ h)

compileOutput : ∀ {n g} (p : C.GateProgram n g) (w : C.WireRef n g) →
  L.Compiled p (λ u → u ≡ w)
compileOutput p w = L.compileSchedule p (λ u → u ≡ w)
  (schedule p (outputMask w) (λ u → u ≡ w) (outputExact w))

pruneCached : ∀ {n} → C.ConcreteBooleanCircuit n → C.ConcreteBooleanCircuit n
pruneCached c =
  let t = compileOutput (C.program c) (C.outputWire c)
  in R.finish (L.Compiled.program t) (L.Compiled.image t (C.outputWire c))

pruneCachedExact : ∀ {n} (c : C.ConcreteBooleanCircuit n) (x : Vec Bool n) →
  C.evaluateCircuit (pruneCached c) x ≡ C.evaluateCircuit c x
pruneCachedExact c x =
  let t = compileOutput (C.program c) (C.outputWire c)
  in trans (R.finishExact (L.Compiled.program t) (L.Compiled.image t (C.outputWire c)) x)
    (L.Compiled.exact t x (C.outputWire c) refl)

pruneCachedBound : ∀ {n} (c : C.ConcreteBooleanCircuit n) →
  C.circuitSize (pruneCached c) ≤ suc (C.circuitSize c)
pruneCachedBound c =
  let t = compileOutput (C.program c) (C.outputWire c)
  in R.finishBound (L.Compiled.program t) (L.Compiled.image t (C.outputWire c)) (L.Compiled.bound t)

-- Zero-gate original input wires are an injective observation bank.
-- Therefore no unrestricted different-consumer collision can be
-- required for EVERY polynomial-width collection of cheap subcircuits.
vecExt : ∀ {n} (x y : Vec Bool n) →
  (∀ i → C.lookupVec i x ≡ C.lookupVec i y) → x ≡ y
vecExt [] [] h = refl
vecExt (x ∷ xs) (y ∷ ys) h with h fzero | vecExt xs ys (λ i → h (fsuc i))
... | refl | refl = refl

inputBankFactors : ∀ {n} (f : Vec Bool n → Bool) (x y : Vec Bool n) →
  (∀ i → C.evaluateCircuit (C.zeroGateInputCircuit i) x ≡
         C.evaluateCircuit (C.zeroGateInputCircuit i) y) → f x ≡ f y
inputBankFactors f x y h = cong f (vecExt x y h)

-- A separation proof must exclude cheap JOINT prefix and suffix
-- realizations; width alone, or arbitrary extensional combine, cannot.
