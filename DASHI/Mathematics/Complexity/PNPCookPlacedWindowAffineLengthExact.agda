module DASHI.Mathematics.Complexity.PNPCookPlacedWindowAffineLengthExact where

-- The coefficients are computed from the actual fixed rejected-row
-- template and the original selector/six-cell Fin renaming.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; cong₂)
import Data.Fin.Base as Fin
import Data.Nat.Properties as N
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as L
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as C
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as D
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as T
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as R
import DASHI.Mathematics.Complexity.ConcreteTapeSelectedRuleWindowCNFExact as S
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as G
import DASHI.Mathematics.Complexity.ConcreteTapeRawGlobalWindowCNFExact as Raw
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalWindowPlacementExact as P
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as E
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.PNPCookAffineSeekGeometryExact as A
import DASHI.Mathematics.Complexity.PNPCookFlattenedPrefixExact as F

record Coeff : Set where
  constructor coeff
  field time column constant : Nat
open Coeff public

eval : Coeff → Nat → Nat → Nat
eval (coeff a b c) t j = a * t + b * j + c

plus : Coeff → Coeff → Coeff
plus (coeff a b c) (coeff x y z) = coeff (a + x) (b + y) (c + z)

inc : Coeff → Coeff
inc (coeff a b c) = coeff a b (suc c)

evalPlus : ∀ x y t j → eval (plus x y) t j ≡ eval x t j + eval y t j
evalPlus (coeff a b c) (coeff x y z) t j =
  solve 8 (λ a b c x y z t j →
    (a :+ x) :* t :+ (b :+ y) :* j :+ (c :+ z) :=
    (a :* t :+ b :* j :+ c) :+ (x :* t :+ y :* j :+ z)) refl a b c x y z t j

evalInc : ∀ x t j → eval (inc x) t j ≡ suc (eval x t j)
evalInc (coeff a b c) t j = N.+-suc (a * t + b * j) c

splitCoeff : ∀ {m n} → (Fin.Fin m → Coeff) → (Fin.Fin n → Coeff) →
  Fin.Fin (m + n) → Coeff
splitCoeff {zero} f g i = g i
splitCoeff {suc m} f g Fin.zero = f Fin.zero
splitCoeff {suc m} f g (Fin.suc i) = splitCoeff (λ k → f (Fin.suc k)) g i

splitExact : ∀ {m n w}
  {f : Fin.Fin m → Coeff} {g : Fin.Fin n → Coeff}
  {p : Fin.Fin m → Fin.Fin w} {q : Fin.Fin n → Fin.Fin w}
  (t j : Nat) →
  (∀ i → Fin.toℕ (p i) ≡ eval (f i) t j) →
  (∀ i → Fin.toℕ (q i) ≡ eval (g i) t j) →
  ∀ i → Fin.toℕ (P.finSumCases p q i) ≡ eval (splitCoeff f g i) t j
splitExact {zero} t j hp hq i = hq i
splitExact {suc m} t j hp hq Fin.zero = hp Fin.zero
splitExact {suc m} t j hp hq (Fin.suc i) =
  splitExact t j (λ k → hp (Fin.suc k)) hq i

module Layout (machine : L.ConcreteTapeMachine) (steps cols : Nat) where

  w = C.CellWidth machine
  row = D.RowBitsWidth machine cols
  rules = R.RuleWidth machine
  rows = T.RowsTraceWidth machine steps cols
  gw = T.GlobalTraceWidth machine steps cols

  selector : Fin.Fin rules → Coeff
  selector i = coeff rules zero (rows + Fin.toℕ i)

  cell : Nat → Nat → Fin.Fin w → Coeff
  cell dt dj i = coeff row w (dt * row + dj * w + Fin.toℕ i)

  six : Fin.Fin (C.WindowWidth machine) → Coeff
  six = splitCoeff (cell 0 0)
    (splitCoeff (cell 0 1)
      (splitCoeff (cell 0 2)
        (splitCoeff (cell 1 0)
          (splitCoeff (cell 1 1) (cell 1 2)))))

  raw : Fin.Fin (S.TransitionLocalWidth machine) → Coeff
  raw = splitCoeff selector six

  selectorExact : ∀ {t} (ts : G.Slot t steps) j i →
    Fin.toℕ (G.globalSelectorRename {machine} {steps} {cols} ts i)
      ≡ eval (selector i) t j
  selectorExact {t} ts j i =
    trans (A.selectorIndex {machine} {steps} {cols} ts i)
      (solve 4 (λ r t s k → s :+ (t :* r :+ k) :=
        r :* t :+ (s :+ k)) refl rules t rows (Fin.toℕ i))

  cellExact : ∀ {t j} (dt dj : Nat)
    (ts : G.Slot (dt + t) (suc steps)) (js : G.Slot (dj + j) cols) i →
    Fin.toℕ (Raw.globalCellRename {machine} {steps} {cols} ts js i)
      ≡ eval (cell dt dj i) t j
  cellExact {t} {j} dt dj ts js i =
    trans (A.cellIndex {machine} {steps} {cols} ts js i)
      (solve 7 (λ dt dj t j r w k →
        (dt :+ t) :* r :+ ((dj :+ j) :* w :+ k) :=
        r :* t :+ w :* j :+ (dt :* r :+ dj :* w :+ k))
        refl dt dj t j row w (Fin.toℕ i))

  sixExact : ∀ {t j} (ts : G.Slot t steps) (js : Raw.WindowStart j cols) i →
    Fin.toℕ (Raw.sixCellGlobalRename {machine} {steps} {cols} ts js i)
      ≡ eval (six i) t j
  sixExact {t} {j} ts js =
    splitExact t j
      (cellExact 0 0 (G.sameSlotInSucc ts) (Raw.windowLeftSlot js))
      (splitExact t j
        (cellExact 0 1 (G.sameSlotInSucc ts) (Raw.windowCenterSlot js))
        (splitExact t j
          (cellExact 0 2 (G.sameSlotInSucc ts) (Raw.windowRightSlot js))
          (splitExact t j
            (cellExact 1 0 (G.nextSlotInSucc ts) (Raw.windowLeftSlot js))
            (splitExact t j
              (cellExact 1 1 (G.nextSlotInSucc ts) (Raw.windowCenterSlot js))
              (cellExact 1 2 (G.nextSlotInSucc ts) (Raw.windowRightSlot js))))))

  rawExact : ∀ {t j} (ts : G.Slot t steps) (js : Raw.WindowStart j cols) i →
    Fin.toℕ (Raw.rawSelectedWindowRename {machine} {steps} {cols} ts js i)
      ≡ eval (raw i) t j
  rawExact {t} {j} ts js = splitExact t j (selectorExact ts j) (sixExact ts js)

  liftedExact : ∀ {t j} (ts : G.Slot t steps) (js : Raw.WindowStart j cols) i →
    Fin.toℕ (E.liftBaseIndex {machine} {steps} {cols}
      (Raw.rawSelectedWindowRename {machine} {steps} {cols} ts js i))
      ≡ eval (raw i) t j
  liftedExact ts js i =
    trans (A.leftIndex _) (rawExact ts js i)

literalCoeff : ∀ {n} → (Fin.Fin n → Coeff) → CNF.Literal n → Coeff
literalCoeff f (CNF.positive i) = inc (inc (f i))
literalCoeff f (CNF.negative i) = inc (inc (inc (f i)))

clauseCoeff : ∀ {n} → (Fin.Fin n → Coeff) → CNF.Clause n → Coeff
clauseCoeff f [] = coeff 0 0 1
clauseCoeff f (l ∷ ls) = inc (plus (literalCoeff f l) (clauseCoeff f ls))

bodyCoeff : ∀ {n} → (Fin.Fin n → Coeff) → CNF.CNF n → Coeff
bodyCoeff f [] = coeff 0 0 0
bodyCoeff f (c ∷ cs) = inc (plus (clauseCoeff f c) (bodyCoeff f cs))

literalExact : ∀ {n m} (f : Fin.Fin n → Coeff) (rename : Fin.Fin n → Fin.Fin m)
  t j (h : ∀ i → Fin.toℕ (rename i) ≡ eval (f i) t j) (l : CNF.Literal n) →
  F.literalWidth (Rename.renameLiteral rename l) ≡ eval (literalCoeff f l) t j
literalExact f rename t j h (CNF.positive i)
  rewrite evalInc (inc (f i)) t j | evalInc (f i) t j | h i = refl
literalExact f rename t j h (CNF.negative i)
  rewrite evalInc (inc (inc (f i))) t j | evalInc (inc (f i)) t j
        | evalInc (f i) t j | h i = refl

clauseExact : ∀ {n m} (f : Fin.Fin n → Coeff) (rename : Fin.Fin n → Fin.Fin m)
  t j (h : ∀ i → Fin.toℕ (rename i) ≡ eval (f i) t j) (c : CNF.Clause n) →
  F.clauseWidth (Rename.renameClause rename c) ≡ eval (clauseCoeff f c) t j
clauseExact f rename t j h [] = refl
clauseExact f rename t j h (l ∷ ls)
  rewrite evalInc (plus (literalCoeff f l) (clauseCoeff f ls)) t j
        | evalPlus (literalCoeff f l) (clauseCoeff f ls) t j
        | literalExact f rename t j h l | clauseExact f rename t j h ls = refl

bodyExact : ∀ {n m} (f : Fin.Fin n → Coeff) (rename : Fin.Fin n → Fin.Fin m)
  t j (h : ∀ i → Fin.toℕ (rename i) ≡ eval (f i) t j) (c : CNF.CNF n) →
  F.bodyWidth (Rename.renameCNF rename c) ≡ eval (bodyCoeff f c) t j
bodyExact f rename t j h [] = refl
bodyExact f rename t j h (c ∷ cs)
  rewrite evalInc (plus (clauseCoeff f c) (bodyCoeff f cs)) t j
        | evalPlus (clauseCoeff f c) (bodyCoeff f cs) t j
        | clauseExact f rename t j h c | bodyExact f rename t j h cs = refl

renameTwice : ∀ {n m k} (f : Fin.Fin n → Fin.Fin m) (g : Fin.Fin m → Fin.Fin k)
  (c : CNF.CNF n) → Rename.renameCNF g (Rename.renameCNF f c)
    ≡ Rename.renameCNF (λ i → g (f i)) c
renameTwice f g [] = refl
renameTwice f g (c ∷ cs) rewrite renameTwice f g cs =
  cong (λ d → d ∷ Rename.renameCNF (λ i → g (f i)) cs) (clauseTwice c)
  where
    clauseTwice : ∀ d → Rename.renameClause g (Rename.renameClause f d)
      ≡ Rename.renameClause (λ i → g (f i)) d
    clauseTwice [] = refl
    clauseTwice (CNF.positive i ∷ ls) rewrite clauseTwice ls = refl
    clauseTwice (CNF.negative i ∷ ls) rewrite clauseTwice ls = refl

module Original (machine : L.ConcreteTapeMachine) (steps cols : Nat)
  (sc : C.EnumerationCoverage (L.finiteState machine))
  (ac : C.EnumerationCoverage (L.finiteSymbol machine))
  (nonempty : R.NonemptyRuleTable machine) where

  module X = Layout machine steps cols

  template : CNF.CNF (S.TransitionLocalWidth machine)
  template = CNF.truthTableCNF
    (S.selectedRuleWindowPredicateWithCoverage {machine = machine} sc ac nonempty)

  block : Coeff
  block = bodyCoeff X.raw template

  actualWindow : ∀ {t j} → G.Slot t steps → Raw.WindowStart j cols →
    CNF.CNF (E.ExtendedGlobalWidth machine steps cols)
  actualWindow ts js = Rename.renameCNF
    (E.liftBaseIndex {machine} {steps} {cols})
    (Raw.rawSelectedWindowCNF {machine} {steps} {cols} sc ac nonempty ts js)

  placedWindowAffineLength : ∀ {t j} (ts : G.Slot t steps) (js : Raw.WindowStart j cols) →
    F.bodyWidth (actualWindow ts js) ≡ eval block t j
  placedWindowAffineLength {t} {j} ts js =
    trans (cong F.bodyWidth (renameTwice
      (Raw.rawSelectedWindowRename {machine} {steps} {cols} ts js)
      (E.liftBaseIndex {machine} {steps} {cols}) template))
      (bodyExact X.raw
        (λ i → E.liftBaseIndex {machine} {steps} {cols}
          (Raw.rawSelectedWindowRename {machine} {steps} {cols} ts js i))
        t j (X.liftedExact ts js) template)

  -- Actual rejected-row order is unchanged: the proof folds over the
  -- original list. Coefficients are computed, not assumed as premises.


-- Assemble the entire original row-major transition conjunction. All
-- widths are computed with the original fixed steps/cols; prefix slices
-- must never recompile at a smaller horizon (that would change indices).
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionConjunctionExact as Enum
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinCNFExact as Global
open import Agda.Builtin.List using (List)

sumMap : ∀ {A : Set} → (A → Nat) → List A → Nat
sumMap f [] = zero
sumMap f (x ∷ xs) = f x + sumMap f xs

sumCong : ∀ {A : Set} (f g : A → Nat) (xs : List A) →
  (∀ x → f x ≡ g x) → sumMap f xs ≡ sumMap g xs
sumCong f g [] h = refl
sumCong f g (x ∷ xs) h rewrite h x | sumCong f g xs h = refl

slotSum : ∀ {n} (a c : Nat) (xs : List (Enum.SomeSlot n)) → Nat
slotSum a c = sumMap (λ x → a * Enum.SomeSlot.index x + c)

shiftSlotSum : ∀ {n} a c (xs : List (Enum.SomeSlot n)) →
  slotSum a c (Enum.mapShiftSlots xs) ≡ slotSum a (a + c) xs
shiftSlotSum a c [] = refl
shiftSlotSum a c (Enum.some-slot i w ∷ xs)
  rewrite shiftSlotSum a c xs =
  cong (_+ slotSum a (a + c) xs)
    (solve 3 (λ a i c → a :* (con 1 :+ i) :+ c :=
      a :* i :+ (a :+ c)) refl a i c)

allSlotSum : ∀ a c n → slotSum a c (Enum.allSlots n) ≡ a * F.tri n + c * n
allSlotSum a c zero =
  solve 2 (λ a c → con 0 := a :* con 0 :+ c :* con 0) refl a c
allSlotSum a c (suc n)
  rewrite shiftSlotSum a c (Enum.allSlots n) | allSlotSum a (a + c) n =
  solve 4 (λ a c n t → (a :* con 0 :+ c) :+
    (a :* t :+ (a :+ c) :* n) :=
    a :* (t :+ n) :+ c :* (con 1 :+ n)) refl a c n (F.tri n)

windowCount : Nat → Nat
windowCount zero = zero
windowCount (suc zero) = zero
windowCount (suc (suc n)) = n

windowSum : ∀ {cols} (a c : Nat) (xs : List (Enum.SomeWindowStart cols)) → Nat
windowSum a c = sumMap (λ x → a * Enum.SomeWindowStart.index x + c)

shiftWindowSum : ∀ {cols} a c (xs : List (Enum.SomeWindowStart cols)) →
  windowSum a c (Enum.mapShiftWindowStarts xs) ≡ windowSum a (a + c) xs
shiftWindowSum a c [] = refl
shiftWindowSum a c (Enum.some-window-start i w ∷ xs)
  rewrite shiftWindowSum a c xs =
  cong (_+ windowSum a (a + c) xs)
    (solve 3 (λ a i c → a :* (con 1 :+ i) :+ c :=
      a :* i :+ (a :+ c)) refl a i c)

allWindowSum : ∀ a c cols →
  windowSum a c (Enum.allWindowStarts cols) ≡
    a * F.tri (windowCount cols) + c * windowCount cols
allWindowSum a c zero = allSlotSum a c zero
allWindowSum a c (suc zero) = allSlotSum a c zero
allWindowSum a c (suc (suc zero)) = allSlotSum a c zero
allWindowSum a c (suc (suc (suc n)))
  rewrite shiftWindowSum a c (Enum.allWindowStarts (suc (suc n)))
        | allWindowSum a (a + c) (suc (suc n)) =
  solve 4 (λ a c n t → (a :* con 0 :+ c) :+
    (a :* t :+ (a :+ c) :* n) :=
    a :* (t :+ n) :+ c :* (con 1 :+ n)) refl a c n (F.tri n)

renameAppend : ∀ {n m} (r : Fin.Fin n → Fin.Fin m) (xs ys : CNF.CNF n) →
  Rename.renameCNF r (Placed.append xs ys) ≡
    L.append (Rename.renameCNF r xs) (Rename.renameCNF r ys)
renameAppend r [] ys = refl
renameAppend r (c ∷ cs) ys rewrite renameAppend r cs ys = refl

compileAppend : ∀ {n m} (xs ys : List (Placed.PlacedPredicate n m)) →
  Placed.compilePlacedAll (Enum.appendPredicates xs ys) ≡
  L.append (Placed.compilePlacedAll xs) (Placed.compilePlacedAll ys)
compileAppend [] ys = refl
compileAppend (p ∷ ps) ys rewrite compileAppend ps ys
  | F.placedAppendSame (Placed.compilePlaced p)
      (L.append (Placed.compilePlacedAll ps) (Placed.compilePlacedAll ys))
  | F.placedAppendSame (Placed.compilePlaced p) (Placed.compilePlacedAll ps) =
  sym (F.appendAssoc (Placed.compilePlaced p) (Placed.compilePlacedAll ps)
    (Placed.compilePlacedAll ys))

renameLocalAppend : ∀ {n m} (r : Fin.Fin n → Fin.Fin m) (xs ys : CNF.CNF n) →
  Rename.renameCNF r (L.append xs ys) ≡
    L.append (Rename.renameCNF r xs) (Rename.renameCNF r ys)
renameLocalAppend r [] ys = refl
renameLocalAppend r (c ∷ cs) ys rewrite renameLocalAppend r cs ys = refl

module Rectangle (machine : L.ConcreteTapeMachine) (steps cols : Nat)
  (sc : C.EnumerationCoverage (L.finiteState machine))
  (ac : C.EnumerationCoverage (L.finiteSymbol machine))
  (nonempty : R.NonemptyRuleTable machine) where

  module O = Original machine steps cols sc ac nonempty

  Pred : Set₁
  Pred = Placed.PlacedPredicate (S.TransitionLocalWidth machine)
    (T.GlobalTraceWidth machine steps cols)

  lifted : List Pred → CNF.CNF (E.ExtendedGlobalWidth machine steps cols)
  lifted ps = Rename.renameCNF (E.liftBaseIndex {machine} {steps} {cols})
    (Placed.compilePlacedAll ps)

  size : List Pred → Nat
  size ps = F.bodyWidth (lifted ps)

  sizeCons : ∀ p ps → size (p ∷ ps) ≡
    F.bodyWidth (Rename.renameCNF (E.liftBaseIndex {machine} {steps} {cols})
      (Placed.compilePlaced p)) + size ps
  sizeCons p ps =
    trans (cong F.bodyWidth (renameAppend (E.liftBaseIndex {machine} {steps} {cols})
      (Placed.compilePlaced p) (Placed.compilePlacedAll ps)))
      (F.bodyWidthAppend _ _)

  sizeAppend : ∀ ps qs → size (Enum.appendPredicates ps qs) ≡ size ps + size qs
  sizeAppend ps qs
    rewrite compileAppend ps qs
          | renameLocalAppend (E.liftBaseIndex {machine} {steps} {cols})
              (Placed.compilePlacedAll ps) (Placed.compilePlacedAll qs) =
    F.bodyWidthAppend _ _

  oneTime : ∀ {t} (ts : G.Slot t steps) (ws : List (Enum.SomeWindowStart cols)) →
    size (Enum.predicatesForOneTime {machine} {steps} {cols} sc ac nonempty ts ws)
    ≡ sumMap (λ x → eval O.block t (Enum.SomeWindowStart.index x)) ws
  oneTime ts [] = refl
  oneTime ts (Enum.some-window-start j js ∷ ws)
    rewrite sizeCons (Raw.rawSelectedWindowPlacedPredicate {machine} {steps} {cols}
      sc ac nonempty ts js)
      (Enum.predicatesForOneTime {machine} {steps} {cols} sc ac nonempty ts ws)
      | O.placedWindowAffineLength ts js | oneTime ts ws = refl

  a = time O.block
  b = column O.block
  c = constant O.block
  J = windowCount cols

  rowWidth : Nat → Nat
  rowWidth t = b * F.tri J + (a * t + c) * J

  evalReorder : ∀ t j → eval O.block t j ≡ b * j + (a * t + c)
  evalReorder t j =
    solve 5 (λ a b c t j → a :* t :+ b :* j :+ c :=
      b :* j :+ (a :* t :+ c)) refl a b c t j

  fullRow : ∀ {t} (ts : G.Slot t steps) →
    size (Enum.predicatesForOneTime {machine} {steps} {cols} sc ac nonempty ts
      (Enum.allWindowStarts cols)) ≡ rowWidth t
  fullRow {t} ts =
    trans (oneTime ts (Enum.allWindowStarts cols))
      (trans (sumCong (λ x → eval O.block t (Enum.SomeWindowStart.index x))
        (λ x → b * Enum.SomeWindowStart.index x + (a * t + c))
        (Enum.allWindowStarts cols) (λ x → evalReorder t (Enum.SomeWindowStart.index x)))
        (allWindowSum b (a * t + c) cols))

  allTimes : ∀ (ts : List (Enum.SomeSlot steps)) →
    size (Enum.predicatesForAllTimes {machine} {steps} {cols} sc ac nonempty ts)
    ≡ sumMap (λ x → rowWidth (Enum.SomeSlot.index x)) ts
  allTimes [] = refl
  allTimes (Enum.some-slot t ts ∷ rest)
    rewrite sizeAppend
      (Enum.predicatesForOneTime {machine} {steps} {cols} sc ac nonempty ts
        (Enum.allWindowStarts cols))
      (Enum.predicatesForAllTimes {machine} {steps} {cols} sc ac nonempty rest)
      | fullRow ts | allTimes rest = refl

  rowReorder : ∀ t → rowWidth t ≡ (J * a) * t + (J * c + b * F.tri J)
  rowReorder t =
    solve 6 (λ a b c J u t → b :* u :+ (a :* t :+ c) :* J :=
      (J :* a) :* t :+ (J :* c :+ b :* u)) refl a b c J (F.tri J) t

  transitionAffineLength :
    F.bodyWidth (Global.liftTransitionCNF {machine} sc ac nonempty steps cols) ≡
      J * (a * F.tri steps + c * steps) + b * steps * F.tri J
  transitionAffineLength =
    trans (allTimes (Enum.allSlots steps))
      (trans (sumCong (λ x → rowWidth (Enum.SomeSlot.index x))
        (λ x → (J * a) * Enum.SomeSlot.index x + (J * c + b * F.tri J))
        (Enum.allSlots steps) (λ x → rowReorder (Enum.SomeSlot.index x)))
        (trans (allSlotSum (J * a) (J * c + b * F.tri J) steps)
          (solve 7 (λ a b c J s u v →
            (J :* a) :* u :+ (J :* c :+ b :* v) :* s :=
            J :* (a :* u :+ c :* s) :+ b :* s :* v)
            refl a b c J steps (F.tri steps) (F.tri J))))

-- Actual full transition body width now follows from the original
-- allSlots/allWindowStarts enumeration, including empty rows/windows.
-- Arbitrary interior prefix and endpoint layout offsets remain separate.


-- Prefix cuts keep the ORIGINAL placement width; take on the already
-- enumerated slots is not recompilation at a shorter horizon.
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.List.Base using (take; drop)
open import Agda.Primitive using (Level)
open import Agda.Builtin.Sigma using (Σ; _,_)

takeSlotsShift : ∀ {n} k (xs : List (Enum.SomeSlot n)) →
  take k (Enum.mapShiftSlots xs) ≡ Enum.mapShiftSlots (take k xs)
takeSlotsShift zero xs = refl
takeSlotsShift (suc k) [] = refl
takeSlotsShift (suc k) (x ∷ xs) rewrite takeSlotsShift k xs = refl

takeWindowsShift : ∀ {n} k (xs : List (Enum.SomeWindowStart n)) →
  take k (Enum.mapShiftWindowStarts xs) ≡ Enum.mapShiftWindowStarts (take k xs)
takeWindowsShift zero xs = refl
takeWindowsShift (suc k) [] = refl
takeWindowsShift (suc k) (x ∷ xs) rewrite takeWindowsShift k xs = refl

slotPrefixSum : ∀ a c k n → k ≤ n →
  slotSum a c (take k (Enum.allSlots n)) ≡ a * F.tri k + c * k
slotPrefixSum a c zero n h = allSlotSum a c zero
slotPrefixSum a c (suc k) (suc n) (s≤s h)
  rewrite takeSlotsShift k (Enum.allSlots n)
        | shiftSlotSum a c (take k (Enum.allSlots n))
        | slotPrefixSum a (a + c) k n h =
  solve 4 (λ a c k u → (a :* con 0 :+ c) :+
    (a :* u :+ (a :+ c) :* k) :=
    a :* (u :+ k) :+ c :* (con 1 :+ k)) refl a c k (F.tri k)

windowPrefixSum : ∀ a c k n → k ≤ windowCount n →
  windowSum a c (take k (Enum.allWindowStarts n)) ≡
    a * F.tri k + c * k
windowPrefixSum a c zero n h = allSlotSum a c zero
windowPrefixSum a c (suc k) (suc (suc (suc n))) (s≤s h)
  rewrite takeWindowsShift k (Enum.allWindowStarts (suc (suc n)))
        | shiftWindowSum a c (take k (Enum.allWindowStarts (suc (suc n))))
        | windowPrefixSum a (a + c) k (suc (suc n)) h =
  solve 4 (λ a c k u → (a :* con 0 :+ c) :+
    (a :* u :+ (a :+ c) :* k) :=
    a :* (u :+ k) :+ c :* (con 1 :+ k)) refl a c k (F.tri k)

-- Indexed witness recovered at the actual list cut.
dropSlotsShift : ∀ {n} k (xs : List (Enum.SomeSlot n)) →
  drop k (Enum.mapShiftSlots xs) ≡ Enum.mapShiftSlots (drop k xs)
dropSlotsShift zero xs = refl
dropSlotsShift (suc k) [] = refl
dropSlotsShift (suc k) (x ∷ xs) = dropSlotsShift k xs

dropWindowsShift : ∀ {n} k (xs : List (Enum.SomeWindowStart n)) →
  drop k (Enum.mapShiftWindowStarts xs) ≡ Enum.mapShiftWindowStarts (drop k xs)
dropWindowsShift zero xs = refl
dropWindowsShift (suc k) [] = refl
dropWindowsShift (suc k) (x ∷ xs) = dropWindowsShift k xs

slotAtCut : ∀ k n → suc k ≤ n →
  Σ (G.Slot k n) (λ w → Σ (List (Enum.SomeSlot n)) (λ rest →
    drop k (Enum.allSlots n) ≡ Enum.some-slot k w ∷ rest))
slotAtCut zero (suc n) h = G.here , Enum.mapShiftSlots (Enum.allSlots n) , refl
slotAtCut (suc k) (suc n) (s≤s h) with slotAtCut k n h
... | w , rest , eq rewrite dropSlotsShift k (Enum.allSlots n) | eq =
  G.there w , Enum.mapShiftSlots rest , refl

windowAtCut : ∀ k n → suc k ≤ windowCount n →
  Σ (Raw.WindowStart k n) (λ w → Σ (List (Enum.SomeWindowStart n)) (λ rest →
    drop k (Enum.allWindowStarts n) ≡ Enum.some-window-start k w ∷ rest))
windowAtCut zero (suc (suc (suc n))) h =
  Raw.here , Enum.mapShiftWindowStarts (Enum.allWindowStarts (suc (suc n))) , refl
windowAtCut (suc k) (suc (suc (suc n))) (s≤s h)
  with windowAtCut k (suc (suc n)) h
... | w , rest , eq rewrite dropWindowsShift k (Enum.allWindowStarts (suc (suc n))) | eq =
  Raw.there w , Enum.mapShiftWindowStarts rest , refl

-- Universe-polymorphic split for the actual placed predicates (Set1).
appendU : ∀ {l : Level} {A : Set l} → List A → List A → List A
appendU [] ys = ys
appendU (x ∷ xs) ys = x ∷ appendU xs ys

takeDrop : ∀ {l : Level} {A : Set l} k (xs : List A) →
  appendU (take k xs) (drop k xs) ≡ xs
takeDrop zero xs = refl
takeDrop (suc k) [] = refl
takeDrop (suc k) (x ∷ xs) = cong (x ∷_) (takeDrop k xs)

module Interior (machine : L.ConcreteTapeMachine) (steps cols : Nat)
  (sc : C.EnumerationCoverage (L.finiteState machine))
  (ac : C.EnumerationCoverage (L.finiteSymbol machine))
  (nonempty : R.NonemptyRuleTable machine) where

  module Q = Rectangle machine steps cols sc ac nonempty
  open Q using (size; lifted; sizeAppend; a; b; c; J; rowWidth)

  timePred = Enum.predicatesForAllTimes {machine} {steps} {cols} sc ac nonempty
  rowPred : ∀ {t} → G.Slot t steps → List (Enum.SomeWindowStart cols) → List Q.Pred
  rowPred ts = Enum.predicatesForOneTime {machine} {steps} {cols} sc ac nonempty ts

  rowAppend : ∀ {t} (ts : G.Slot t steps) xs ys →
    rowPred ts (appendU xs ys) ≡ Enum.appendPredicates (rowPred ts xs) (rowPred ts ys)
  rowAppend ts [] ys = refl
  rowAppend ts (x ∷ xs) ys rewrite rowAppend ts xs ys = refl

  predAssoc : ∀ (xs ys zs : List Q.Pred) →
    Enum.appendPredicates (Enum.appendPredicates xs ys) zs ≡
    Enum.appendPredicates xs (Enum.appendPredicates ys zs)
  predAssoc [] ys zs = refl
  predAssoc (x ∷ xs) ys zs rewrite predAssoc xs ys zs = refl

  timeAppend : ∀ xs ys →
    timePred (appendU xs ys) ≡ Enum.appendPredicates (timePred xs) (timePred ys)
  timeAppend [] ys = refl
  timeAppend (Enum.some-slot t ts ∷ xs) ys rewrite timeAppend xs ys =
    sym (predAssoc (rowPred ts (Enum.allWindowStarts cols)) (timePred xs) (timePred ys))

  priorRows t = timePred (take t (Enum.allSlots steps))

  priorWindows : ∀ {t} → G.Slot t steps → Nat → List Q.Pred
  priorWindows ts j = rowPred ts (take j (Enum.allWindowStarts cols))

  rowOffset t = J * (a * F.tri t + c * t) + b * t * F.tri J
  columnOffset t j = j * (a * t + c) + b * F.tri j

  rowsWidth : ∀ t → t ≤ steps → size (priorRows t) ≡ rowOffset t
  rowsWidth t ht =
    trans (Q.allTimes (take t (Enum.allSlots steps)))
      (trans (sumCong (λ x → rowWidth (Enum.SomeSlot.index x))
        (λ x → (J * a) * Enum.SomeSlot.index x + (J * c + b * F.tri J))
        (take t (Enum.allSlots steps)) (λ x → Q.rowReorder (Enum.SomeSlot.index x)))
        (trans (slotPrefixSum (J * a) (J * c + b * F.tri J) t steps ht)
          (solve 7 (λ a b c J t u v →
            (J :* a) :* u :+ (J :* c :+ b :* v) :* t :=
            J :* (a :* u :+ c :* t) :+ b :* t :* v)
            refl a b c J t (F.tri t) (F.tri J))))

  windowsWidth : ∀ {t} (ts : G.Slot t steps) j → j ≤ J →
    size (priorWindows ts j) ≡ columnOffset t j
  windowsWidth {t} ts j hj =
    trans (Q.oneTime ts (take j (Enum.allWindowStarts cols)))
      (trans (sumCong (λ x → eval Q.O.block t (Enum.SomeWindowStart.index x))
        (λ x → b * Enum.SomeWindowStart.index x + (a * t + c))
        (take j (Enum.allWindowStarts cols)) (λ x → Q.evalReorder t (Enum.SomeWindowStart.index x)))
        (trans (windowPrefixSum b (a * t + c) j cols hj)
          (solve 4 (λ b u j v → b :* u :+ v :* j := j :* v :+ b :* u)
            refl b (F.tri j) j (a * t + c))))

  prefix : ∀ {t} → G.Slot t steps → Nat → List Q.Pred
  prefix {t} ts j = Enum.appendPredicates (priorRows t) (priorWindows ts j)

  prefixWidth : ∀ {t} (ts : G.Slot t steps) j → t ≤ steps → j ≤ J →
    size (prefix ts j) ≡ rowOffset t + columnOffset t j
  prefixWidth {t} ts j ht hj =
    trans (sizeAppend (priorRows t) (priorWindows ts j))
      (cong₂ _+_ (rowsWidth t ht) (windowsWidth ts j hj))

  suffix : ∀ {t} → G.Slot t steps → Nat → List (Enum.SomeSlot steps) → List Q.Pred
  suffix ts j rest = Enum.appendPredicates
    (rowPred ts (drop j (Enum.allWindowStarts cols))) (timePred rest)

  -- Row and column cuts refer to the original enumerated list, so
  -- actual compiler order (including all duplicate clauses) is preserved.
  predicateSplit : ∀ {t} (ts : G.Slot t steps) j rest →
    drop t (Enum.allSlots steps) ≡ Enum.some-slot t ts ∷ rest →
    Enum.allGlobalTransitionPredicates {machine} sc ac nonempty steps cols ≡
    Enum.appendPredicates (prefix ts j) (suffix ts j rest)
  predicateSplit {t} ts j rest h =
    trans (cong timePred (sym (takeDrop t (Enum.allSlots steps))))
      (trans (timeAppend (take t (Enum.allSlots steps)) (drop t (Enum.allSlots steps)))
        (trans (cong (Enum.appendPredicates (priorRows t)) (cong timePred h))
          (trans (cong (λ z → Enum.appendPredicates (priorRows t)
              (Enum.appendPredicates z (timePred rest)))
              (trans (cong (rowPred ts) (sym (takeDrop j (Enum.allWindowStarts cols))))
                (rowAppend ts (take j (Enum.allWindowStarts cols))
                  (drop j (Enum.allWindowStarts cols)))))
            (trans (cong (Enum.appendPredicates (priorRows t))
                (predAssoc (priorWindows ts j)
                  (rowPred ts (drop j (Enum.allWindowStarts cols))) (timePred rest)))
              (sym (predAssoc (priorRows t) (priorWindows ts j) (suffix ts j rest)))))))

  liftedAppend : ∀ ps qs → lifted (Enum.appendPredicates ps qs) ≡
    L.append (lifted ps) (lifted qs)
  liftedAppend ps qs
    rewrite compileAppend ps qs =
      renameLocalAppend (E.liftBaseIndex {machine} {steps} {cols})
        (Placed.compilePlacedAll ps) (Placed.compilePlacedAll qs)

  actualTransitionSplit : ∀ {t} (ts : G.Slot t steps) j rest →
    drop t (Enum.allSlots steps) ≡ Enum.some-slot t ts ∷ rest →
    Global.liftTransitionCNF {machine} sc ac nonempty steps cols ≡
      L.append (lifted (prefix ts j)) (lifted (suffix ts j rest))
  actualTransitionSplit ts j rest h =
    trans (cong lifted (predicateSplit ts j rest h))
      (liftedAppend (prefix ts j) (suffix ts j rest))


-- The original stream starts with transition clauses, then initial
-- units, then acceptance. Bit offsets multiply TOKEN widths by three.
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingBitFrontier as Cursor
import DASHI.Mathematics.Complexity.CanonicalVirtualFormulaBitSourceExact as Lookup
import DASHI.Mathematics.Complexity.CNFCookPrefixTokenExact as Tokens

module StreamCut (machine : L.ConcreteTapeMachine) (steps cols : Nat)
  (sc : C.EnumerationCoverage (L.finiteState machine))
  (ac : C.EnumerationCoverage (L.finiteSymbol machine))
  (nonempty : R.NonemptyRuleTable machine)
  (initial : CNF.Bits (D.RowBitsWidth machine cols)) where

  module I = Interior machine steps cols sc ac nonempty
  open I using (prefix; suffix; rowOffset; columnOffset; prefixWidth)
  open I.Q using (lifted; size; J)

  endpoints : CNF.CNF (E.ExtendedGlobalWidth machine steps cols)
  endpoints = Placed.append (E.initialEndpointCNF {machine} {steps} {cols} initial)
    (E.acceptingEndpointCNF {machine} {steps} {cols} sc ac)

  globalSplit : ∀ {t} (ts : G.Slot t steps) j rest →
    drop t (Enum.allSlots steps) ≡ Enum.some-slot t ts ∷ rest →
    Global.globalCookLevinCNF {machine} sc ac nonempty steps cols initial ≡
    L.append (lifted (prefix ts j)) (L.append (lifted (suffix ts j rest)) endpoints)
  globalSplit ts j rest h =
    trans (F.transitionSectionSplit sc ac nonempty steps cols initial)
      (trans (cong (λ xs → L.append xs endpoints)
        (I.actualTransitionSplit ts j rest h))
        (F.appendAssoc (lifted (prefix ts j)) (lifted (suffix ts j rest)) endpoints))

  streamedInterior : ∀ {t} (ts : G.Slot t steps) j rest k
    (ht : t ≤ steps) (hj : j ≤ J) →
    drop t (Enum.allSlots steps) ≡ Enum.some-slot t ts ∷ rest →
    Cursor.streamedCookBit sc ac nonempty steps cols initial
      (3 * (rowOffset t + columnOffset t j) + k)
    ≡ Lookup.lookupBit k (Tokens.cnfTokenBits
      (L.append (lifted (suffix ts j rest)) endpoints))
  streamedInterior ts j rest k ht hj h
    rewrite sym (prefixWidth ts j ht hj) =
    F.streamedAtSplit sc ac nonempty steps cols initial
      (lifted (prefix ts j)) (L.append (lifted (suffix ts j rest)) endpoints)
      k (globalSplit ts j rest h)

  -- At an admissible cut, windowAtCut identifies the head of this
  -- exact suffix. The local token seeker may then use its original
  -- clause order. No materialized prefix is needed in the arithmetic model.

-- Actual initial unit section length, including the negative-literal
-- count. The generic index-offset hypothesis is discharged below by
-- the existing row-zero Fin placement identity.
open import Agda.Builtin.Bool using (Bool; true; false)

zeroCount : ∀ {n} → CNF.Bits n → Nat
zeroCount CNF.[]ᵇ = zero
zeroCount (false CNF.∷ᵇ xs) = suc (zeroCount xs)
zeroCount (true CNF.∷ᵇ xs) = zeroCount xs

unitWidthExact : ∀ {n m} (rename : Fin.Fin n → Fin.Fin m)
  (p : Nat) (bits : CNF.Bits n) →
  (∀ i → Fin.toℕ (rename i) ≡ p + Fin.toℕ i) →
  F.bodyWidth (E.unitClausesForTarget rename bits) ≡
    F.tri n + (p + 5) * n + zeroCount bits
unitWidthExact {zero} rename p CNF.[]ᵇ h =
  solve 1 (λ p → con 0 := con 0 :+ (p :+ con 5) :* con 0 :+ con 0) refl p
unitWidthExact {suc n} rename p (false CNF.∷ᵇ bits) h
  rewrite h Fin.zero | unitWidthExact (λ i → rename (Fin.suc i)) (suc p) bits next =
  solve 4 (λ p n t z → con 6 :+ p :+
    (t :+ (con 1 :+ p :+ con 5) :* n :+ z) :=
    (t :+ n) :+ (p :+ con 5) :* (con 1 :+ n) :+ (con 1 :+ z))
    refl p n (F.tri n) (zeroCount bits)
  where
    next : ∀ i → Fin.toℕ (rename (Fin.suc i)) ≡ suc p + Fin.toℕ i
    next i = trans (h (Fin.suc i)) (N.+-suc p (Fin.toℕ i))
unitWidthExact {suc n} rename p (true CNF.∷ᵇ bits) h
  rewrite h Fin.zero | unitWidthExact (λ i → rename (Fin.suc i)) (suc p) bits next =
  solve 4 (λ p n t z → con 5 :+ p :+ (t :+ (con 1 :+ p :+ con 5) :* n :+ z) :=
    (t :+ n) :+ (p :+ con 5) :* (con 1 :+ n) :+ z)
    refl p n (F.tri n) (zeroCount bits)
  where
    next : ∀ i → Fin.toℕ (rename (Fin.suc i)) ≡ suc p + Fin.toℕ i
    next i = trans (h (Fin.suc i)) (N.+-suc p (Fin.toℕ i))

initialWidthExact : ∀ {machine steps cols}
  (bits : CNF.Bits (D.RowBitsWidth machine cols)) →
  F.bodyWidth (E.initialEndpointCNF {machine} {steps} {cols} bits) ≡
    F.tri (D.RowBitsWidth machine cols) + 5 * D.RowBitsWidth machine cols + zeroCount bits
initialWidthExact {machine} {steps} {cols} bits =
  unitWidthExact (E.initialRowExtendedRename {machine} {steps} {cols}) zero bits
    (λ i → trans (A.leftIndex _) (A.rowIndex {machine} {steps} {cols} G.here i))
