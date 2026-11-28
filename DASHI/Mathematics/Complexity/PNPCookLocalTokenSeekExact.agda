module DASHI.Mathematics.Complexity.PNPCookLocalTokenSeekExact where

-- Attach the actual CNF grammar, original literal seek and flattened
-- widths. Skip whole unary literal spans without materializing tokens.
-- This is the local-template proof required by the compact section
-- inverter, not the physical implementation of that inverter.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Agda.Builtin.Nat as Nat
import Data.Nat.Properties as N
import Data.Fin.Base as Fin
import DASHI.Mathematics.Complexity.PNPCookAffineSeekGeometryExact as S
import DASHI.Mathematics.Complexity.PNPCookFlattenedPrefixExact as F
import DASHI.Mathematics.Complexity.CNFCookPrefixTokenExact as T
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact as P
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as B
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as L
import DASHI.Mathematics.Complexity.CanonicalVirtualFormulaBitSourceExact as Lookup
open S using (if_then_else_)

lookupSplit : ∀ {A : Set} (xs ys : List A) k →
  S.lookup k (L.append xs ys) ≡
  (if Nat._<_ k (P.listLength xs) then S.lookup k xs
    else S.lookup (Nat._-_ k (P.listLength xs)) ys)
lookupSplit [] ys zero = refl
lookupSplit [] ys (suc k) = refl
lookupSplit (x ∷ xs) ys zero = refl
lookupSplit (x ∷ xs) ys (suc k) = lookupSplit xs ys k

lookupSplitWidth : ∀ {A : Set} (xs ys : List A) k w →
  P.listLength xs ≡ w →
  S.lookup k (L.append xs ys) ≡
  (if Nat._<_ k w then S.lookup k xs else S.lookup (Nat._-_ k w) ys)
lookupSplitWidth xs ys k .(P.listLength xs) refl = lookupSplit xs ys k

literalEmptyLength : ∀ {n} (l : CNF.Literal n) →
  P.listLength (T.literalTokensInto l []) ≡ F.literalWidth l
literalEmptyLength l =
  trans (F.literalLength l []) (N.+-identityʳ (F.literalWidth l))

clauseEmptyLength : ∀ {n} (c : CNF.Clause n) →
  P.listLength (T.clauseTokensInto c []) ≡ F.clauseWidth c
clauseEmptyLength c =
  trans (F.clauseLength c []) (N.+-identityʳ (F.clauseWidth c))

clauseSeek : ∀ {n} → CNF.Clause n → Nat →
  List P.CookSyntaxToken → Maybe P.CookSyntaxToken
clauseSeek [] zero rest = just P.formulaFalseToken
clauseSeek [] (suc k) rest = S.lookup k rest
clauseSeek (l ∷ ls) zero rest = just P.formulaOrToken
clauseSeek (l ∷ ls) (suc k) rest =
  if Nat._<_ k (F.literalWidth l) then S.literalSeek l k []
  else clauseSeek ls (Nat._-_ k (F.literalWidth l)) rest

clauseSeekExact : ∀ {n} (c : CNF.Clause n) k rest →
  clauseSeek c k rest ≡ S.lookup k (T.clauseTokensInto c rest)
clauseSeekExact [] zero rest = refl
clauseSeekExact [] (suc k) rest = refl
clauseSeekExact (l ∷ ls) zero rest = refl
clauseSeekExact (l ∷ ls) (suc k) rest
  rewrite S.literalSeekExact l k []
        | clauseSeekExact ls (Nat._-_ k (F.literalWidth l)) rest =
  sym (trans (cong (S.lookup k) (F.literalAppend l [] (T.clauseTokensInto ls rest)))
    (lookupSplitWidth (T.literalTokensInto l []) (T.clauseTokensInto ls rest)
      k (F.literalWidth l) (literalEmptyLength l)))

cnfSeek : ∀ {n} → CNF.CNF n → Nat →
  List P.CookSyntaxToken → Maybe P.CookSyntaxToken
cnfSeek [] zero rest = just P.formulaTrueToken
cnfSeek [] (suc k) rest = S.lookup k rest
cnfSeek (c ∷ cs) zero rest = just P.formulaAndToken
cnfSeek (c ∷ cs) (suc k) rest =
  if Nat._<_ k (F.clauseWidth c) then clauseSeek c k []
  else cnfSeek cs (Nat._-_ k (F.clauseWidth c)) rest

cnfSeekExact : ∀ {n} (f : CNF.CNF n) k rest →
  cnfSeek f k rest ≡ S.lookup k (T.cnfTokensInto f rest)
cnfSeekExact [] zero rest = refl
cnfSeekExact [] (suc k) rest = refl
cnfSeekExact (c ∷ cs) zero rest = refl
cnfSeekExact (c ∷ cs) (suc k) rest
  rewrite clauseSeekExact c k []
        | cnfSeekExact cs (Nat._-_ k (F.clauseWidth c)) rest =
  sym (trans (cong (S.lookup k) (F.clauseAppend c [] (T.cnfTokensInto cs rest)))
    (lookupSplitWidth (T.clauseTokensInto c []) (T.cnfTokensInto cs rest)
      k (F.clauseWidth c) (clauseEmptyLength c)))

-- Exact three-bit consumer, using a bounded offset instead of another
-- full stream. The binary index inversion itself is separate.
tokenBit : Maybe P.CookSyntaxToken → Fin.Fin 3 → Maybe Bool
tokenBit nothing j = nothing
tokenBit (just t) j = S.lookup (Fin.toℕ j) (B.tokenBits t)

lookupEmpty : ∀ {A : Set} k → S.lookup {A = A} k [] ≡ nothing
lookupEmpty zero = refl
lookupEmpty (suc k) = refl

lookupSame : ∀ k xs → S.lookup k xs ≡ Lookup.lookupBit k xs
lookupSame zero [] = refl
lookupSame zero (x ∷ xs) = refl
lookupSame (suc k) [] = refl
lookupSame (suc k) (x ∷ xs) = lookupSame k xs

headThree : ∀ (a b c : Bool) (j : Fin.Fin 3) xs →
  S.lookup (Fin.toℕ j) (a ∷ b ∷ c ∷ xs) ≡
  S.lookup (Fin.toℕ j) (a ∷ b ∷ c ∷ [])
headThree a b c Fin.zero xs = refl
headThree a b c (Fin.suc Fin.zero) xs = refl
headThree a b c (Fin.suc (Fin.suc Fin.zero)) xs = refl

headToken : ∀ t j xs →
  S.lookup (Fin.toℕ j) (B.append (B.tokenBits t) xs) ≡
  S.lookup (Fin.toℕ j) (B.tokenBits t)
headToken P.natZeroToken j xs = headThree false false false j xs
headToken P.natSuccToken j xs = headThree false false true j xs
headToken P.formulaVariableToken j xs = headThree false true false j xs
headToken P.formulaFalseToken j xs = headThree false true true j xs
headToken P.formulaTrueToken j xs = headThree true false false j xs
headToken P.formulaNegateToken j xs = headThree true false true j xs
headToken P.formulaAndToken j xs = headThree true true false j xs
headToken P.formulaOrToken j xs = headThree true true true j xs

skipBits : ∀ (xs ys : List Bool) k →
  S.lookup (B.listLength xs + k) (B.append xs ys) ≡ S.lookup k ys
skipBits [] ys k = refl
skipBits (x ∷ xs) ys k = skipBits xs ys k

skipToken : ∀ t ts k →
  S.lookup (3 + k) (B.encodeTokenStream (t ∷ ts)) ≡
  S.lookup k (B.encodeTokenStream ts)
skipToken t ts k rewrite sym (B.tokenBitsLength t) =
  skipBits (B.tokenBits t) (B.encodeTokenStream ts) k

tokenStreamBit : ∀ ts k (j : Fin.Fin 3) →
  tokenBit (S.lookup k ts) j ≡
  S.lookup (k * 3 + Fin.toℕ j) (B.encodeTokenStream ts)
tokenStreamBit [] k j
  rewrite lookupEmpty {A = P.CookSyntaxToken} k
        | lookupEmpty {A = Bool} (k * 3 + Fin.toℕ j) = refl
tokenStreamBit (t ∷ ts) zero j =
  sym (headToken t j (B.encodeTokenStream ts))
tokenStreamBit (t ∷ ts) (suc k) j =
  trans (tokenStreamBit ts k j)
    (sym (skipToken t ts (k * 3 + Fin.toℕ j)))

seekSerialized : ∀ {n} → CNF.CNF n → Nat → Fin.Fin 3 → Maybe Bool
seekSerialized f k j = tokenBit (cnfSeek f k []) j

seekSerializedExact : ∀ {n} (f : CNF.CNF n) k (j : Fin.Fin 3) →
  seekSerialized f k j ≡ Lookup.lookupBit (3 * k + Fin.toℕ j) (T.cnfTokenBits f)
seekSerializedExact f k j rewrite cnfSeekExact f k [] | N.*-comm 3 k =
  trans (tokenStreamBit (T.cnfTokens f) k j)
    (lookupSame (k * 3 + Fin.toℕ j) (T.cnfTokenBits f))

-- Kernel pending. Native full repeated-window arithmetic and actual
-- standard tape resource closure still separate.
