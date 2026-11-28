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
