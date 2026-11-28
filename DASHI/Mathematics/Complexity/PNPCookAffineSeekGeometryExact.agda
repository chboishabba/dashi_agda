module DASHI.Mathematics.Complexity.PNPCookAffineSeekGeometryExact where

-- Actual local template extraction and numeric slot placement. Classical
-- affine index arithmetic; same original Cook formula and token encoding.
-- The full arithmetic bit-seek / native machine clock weld is separate.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Base using (_≤_; s≤s)
import Data.Nat.Properties as N
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import Data.Fin.Base as Fin
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as L
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as C
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalWindowPlacementExact as P
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as G
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as R
import DASHI.Mathematics.Complexity.ConcreteTapeSelectedRuleWindowCNFExact as S
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as E
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as D
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as T
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as I
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.GuardedCookBitQueryCodeExact as Q
import DASHI.Mathematics.Complexity.GuardedCookBitQueryLengthExact as QL
import DASHI.Mathematics.Complexity.PNotEqualsNPVirtualQuotationFrontierExact as V

leftIndex : ∀ {m n} (i : Fin.Fin m) →
  Fin.toℕ (P.finLeft {m} {n} i) ≡ Fin.toℕ i
leftIndex {zero} ()
leftIndex {suc m} Fin.zero = refl
leftIndex {suc m} (Fin.suc i) = cong suc (leftIndex i)

rightIndex : ∀ m {n} (i : Fin.Fin n) →
  Fin.toℕ (P.finRight m i) ≡ m + Fin.toℕ i
rightIndex zero i = refl
rightIndex (suc m) i = cong suc (rightIndex m i)

blockIndex : ∀ {k count width} (slot : G.Slot k count) (i : Fin.Fin width) →
  Fin.toℕ (G.blockRename slot i) ≡ k * width + Fin.toℕ i
blockIndex G.here i = leftIndex i
blockIndex {k = suc k} {width = width} (G.there slot) i =
  trans (rightIndex width (G.blockRename slot i))
    (trans (cong (width +_) (blockIndex slot i))
      (sym (N.+-assoc width (k * width) (Fin.toℕ i))))

rowIndex : ∀ {machine steps cols k}
  (slot : G.Slot k (suc steps)) (i : Fin.Fin (D.RowBitsWidth machine cols)) →
  Fin.toℕ (G.globalRowRename {machine} {steps} {cols} slot i)
  ≡ k * D.RowBitsWidth machine cols + Fin.toℕ i
rowIndex slot i = trans (leftIndex _) (blockIndex slot i)

selectorIndex : ∀ {machine steps cols k}
  (slot : G.Slot k steps) (i : Fin.Fin (R.RuleWidth machine)) →
  Fin.toℕ (G.globalSelectorRename {machine} {steps} {cols} slot i)
  ≡ T.RowsTraceWidth machine steps cols + (k * R.RuleWidth machine + Fin.toℕ i)
selectorIndex {machine} {steps} {cols} slot i =
  trans (rightIndex (T.RowsTraceWidth machine steps cols) _)
    (cong (T.RowsTraceWidth machine steps cols +_) (blockIndex slot i))

cellIndex : ∀ {machine steps cols t j}
  (time : G.Slot t (suc steps)) (column : G.Slot j cols)
  (i : Fin.Fin (C.CellWidth machine)) →
  Fin.toℕ (G.globalRowRename {machine} {steps} {cols} time
    (G.blockRename column i))
  ≡ t * D.RowBitsWidth machine cols + (j * C.CellWidth machine + Fin.toℕ i)
cellIndex {machine} {steps} {cols} {t} time column i =
  trans (rowIndex time (G.blockRename column i))
    (cong (t * D.RowBitsWidth machine cols +_) (blockIndex column i))

Literal : Set
Literal = Nat × Bool

literal : ∀ {n} → CNF.Literal n → Literal
literal (CNF.positive i) = Fin.toℕ i , true
literal (CNF.negative i) = Fin.toℕ i , false

clause : ∀ {n} → CNF.Clause n → List Literal
clause [] = []
clause (l ∷ ls) = literal l ∷ clause ls

clauses : ∀ {n} → CNF.CNF n → List (List Literal)
clauses [] = []
clauses (c ∷ cs) = clause c ∷ clauses cs

bits : ∀ {n} → CNF.Bits n → List Bool
bits CNF.[]ᵇ = []
bits (b CNF.∷ᵇ bs) = b ∷ bits bs

module Export {machine : L.ConcreteTapeMachine}
  (sc : C.EnumerationCoverage (L.finiteState machine))
  (ac : C.EnumerationCoverage (L.finiteSymbol machine))
  (nonempty : R.NonemptyRuleTable machine) where

  transitionTemplate : List (List Literal)
  transitionTemplate = clauses
    (CNF.truthTableCNF
      (S.selectedRuleWindowPredicateWithCoverage {machine = machine} sc ac nonempty))

  acceptanceTemplate : List (List Literal)
  acceptanceTemplate = clauses
    (CNF.truthTableCNF (E.witnessAcceptingPredicate {machine = machine} sc ac))

  blankPattern : List Bool
  blankPattern = bits (C.encodeCell {machine} sc ac (L.plain (L.blank machine)))

  cellPatterns : List (L.TapeCell (L.State machine) (L.Symbol machine)) → List Bool
  cellPatterns [] = []
  cellPatterns (c ∷ cs) = L.append (bits (C.encodeCell {machine} sc ac c)) (cellPatterns cs)

  middlePattern : I.InputWord machine → List Bool
  middlePattern input = cellPatterns (I.initialInputCells {machine} input)

-- The old FULL unary query charge cannot fit even once in its own T.
-- This is not a claim that every embeddedCallSteps pays queryCharge:
-- that additional payment premise must be supplied by the compiler.
fullQueryChargeStrict : ∀ {presentation}
  (generator : V.UniversalGuardedCookBitGenerator presentation)
  (query : Q.GuardedCookBitQuery) →
  suc (Q.steps query) ≤ V.queryCharge generator query
fullQueryChargeStrict generator query =
  N.≤-trans
    (QL.unarySectionBelowQueryLength query (Q.steps query)
      refl (QL.stepsSectionMember query))
    (N.m≤m+n (Q.queryBitLength query) (V.querySteps generator query))

sucNotLeSelf : ∀ n → suc n ≤ n → ⊥
sucNotLeSelf zero ()
sucNotLeSelf (suc n) (s≤s p) = sucNotLeSelf n p

fullQueryCannotFit : ∀ {presentation}
  (generator : V.UniversalGuardedCookBitGenerator presentation)
  (query : Q.GuardedCookBitQuery) →
  V.queryCharge generator query ≤ Q.steps query → ⊥
fullQueryCannotFit generator query fit = sucNotLeSelf (Q.steps query)
  (N.≤-trans (fullQueryChargeStrict generator query) fit)


-- Exact direct seek through the actual unary variable-index token run.
-- Proof recursion is on the specification; the executable function uses
-- comparisons and subtraction instead of constructing the token list.
import Agda.Builtin.Nat as Nat
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact as Prefix
import DASHI.Mathematics.Complexity.CNFCookPrefixTokenExact as Tokens

lookup : ∀ {A : Set} → Nat → List A → Maybe A
lookup zero [] = nothing
lookup zero (x ∷ xs) = just x
lookup (suc i) [] = nothing
lookup (suc i) (x ∷ xs) = lookup i xs

if_then_else_ : ∀ {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

natSeek : Nat → Nat → List Prefix.CookSyntaxToken → Maybe Prefix.CookSyntaxToken
natSeek n i rest =
  if Nat._<_ i n then just Prefix.natSuccToken
  else if Nat._<_ n i then lookup (Nat._-_ i (suc n)) rest
  else just Prefix.natZeroToken

natSeekExact : ∀ n i rest →
  natSeek n i rest ≡ lookup i (Prefix.encodeNatInto n rest)
natSeekExact zero zero rest = refl
natSeekExact zero (suc i) rest = refl
natSeekExact (suc n) zero rest = refl
natSeekExact (suc n) (suc i) rest = natSeekExact n i rest

literalSeek : ∀ {n} → CNF.Literal n → Nat →
  List Prefix.CookSyntaxToken → Maybe Prefix.CookSyntaxToken
literalSeek (CNF.positive i) zero rest = just Prefix.formulaVariableToken
literalSeek (CNF.positive i) (suc k) rest = natSeek (Fin.toℕ i) k rest
literalSeek (CNF.negative i) zero rest = just Prefix.formulaNegateToken
literalSeek (CNF.negative i) (suc zero) rest = just Prefix.formulaVariableToken
literalSeek (CNF.negative i) (suc (suc k)) rest = natSeek (Fin.toℕ i) k rest

literalSeekExact : ∀ {n} (l : CNF.Literal n) k rest →
  literalSeek l k rest ≡ lookup k (Tokens.literalTokensInto l rest)
literalSeekExact (CNF.positive i) zero rest = refl
literalSeekExact (CNF.positive i) (suc k) rest = natSeekExact (Fin.toℕ i) k rest
literalSeekExact (CNF.negative i) zero rest = refl
literalSeekExact (CNF.negative i) (suc zero) rest = refl
literalSeekExact (CNF.negative i) (suc (suc k)) rest = natSeekExact (Fin.toℕ i) k rest
