module DASHI.Mathematics.Complexity.PNPCookFlattenedPrefixExact where

-- The actual CNF grammar has one terminal TRUE, not one per window.
-- A body prefix contains AND and clause tokens but NO terminal TRUE.
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import Data.Nat.Properties as N
import Data.Fin.Base as Fin
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact as P
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as B
import DASHI.Mathematics.Complexity.CNFCookPrefixTokenExact as T
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingBitExact as Stream
import DASHI.Mathematics.Complexity.CanonicalVirtualFormulaBitSourceExact as Lookup
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as L

natCount : ∀ n → P.natTokenCount n ≡ suc n
natCount zero = refl
natCount (suc n) = cong suc (natCount n)

literalWidth : ∀ {n} → CNF.Literal n → Nat
literalWidth (CNF.positive i) = suc (suc (Fin.toℕ i))
literalWidth (CNF.negative i) = suc (suc (suc (Fin.toℕ i)))

literalLength : ∀ {n} (l : CNF.Literal n) rest →
  P.listLength (T.literalTokensInto l rest) ≡ literalWidth l + P.listLength rest
literalLength (CNF.positive i) rest
  rewrite P.encodeNatIntoLength (Fin.toℕ i) rest | natCount (Fin.toℕ i) = refl
literalLength (CNF.negative i) rest
  rewrite P.encodeNatIntoLength (Fin.toℕ i) rest | natCount (Fin.toℕ i) = refl

clauseWidth : ∀ {n} → CNF.Clause n → Nat
clauseWidth [] = suc zero
clauseWidth (l ∷ ls) = suc (literalWidth l + clauseWidth ls)

clauseLength : ∀ {n} (c : CNF.Clause n) rest →
  P.listLength (T.clauseTokensInto c rest) ≡ clauseWidth c + P.listLength rest
clauseLength [] rest = refl
clauseLength (l ∷ ls) rest
  rewrite literalLength l (T.clauseTokensInto ls rest) | clauseLength ls rest =
  cong suc (sym (N.+-assoc (literalWidth l) (clauseWidth ls) (P.listLength rest)))

bodyWidth : ∀ {n} → CNF.CNF n → Nat
bodyWidth [] = zero
bodyWidth (c ∷ cs) = suc (clauseWidth c + bodyWidth cs)

bodyInto : ∀ {n} → CNF.CNF n → List P.CookSyntaxToken → List P.CookSyntaxToken
bodyInto [] rest = rest
bodyInto (c ∷ cs) rest = P.formulaAndToken ∷ T.clauseTokensInto c (bodyInto cs rest)

bodyLength : ∀ {n} (f : CNF.CNF n) rest →
  P.listLength (bodyInto f rest) ≡ bodyWidth f + P.listLength rest
bodyLength [] rest = refl
bodyLength (c ∷ cs) rest
  rewrite clauseLength c (bodyInto cs rest) | bodyLength cs rest =
  cong suc (sym (N.+-assoc (clauseWidth c) (bodyWidth cs) (P.listLength rest)))

bodyCompose : ∀ {n} (f g : CNF.CNF n) rest →
  bodyInto (L.append f g) rest ≡ bodyInto f (bodyInto g rest)
bodyCompose [] g rest = refl
bodyCompose (c ∷ cs) g rest rewrite bodyCompose cs g rest = refl

actualTokens : ∀ {n} (f : CNF.CNF n) rest →
  T.cnfTokensInto f rest ≡ bodyInto f (P.formulaTrueToken ∷ rest)
actualTokens [] rest = refl
actualTokens (c ∷ cs) rest rewrite actualTokens cs rest = refl

natAppend : ∀ n xs ys → P.encodeNatInto n (L.append xs ys)
  ≡ L.append (P.encodeNatInto n xs) ys
natAppend zero xs ys = refl
natAppend (suc n) xs ys rewrite natAppend n xs ys = refl

literalAppend : ∀ {n} (l : CNF.Literal n) xs ys →
  T.literalTokensInto l (L.append xs ys) ≡ L.append (T.literalTokensInto l xs) ys
literalAppend (CNF.positive i) xs ys rewrite natAppend (Fin.toℕ i) xs ys = refl
literalAppend (CNF.negative i) xs ys rewrite natAppend (Fin.toℕ i) xs ys = refl

clauseAppend : ∀ {n} (c : CNF.Clause n) xs ys →
  T.clauseTokensInto c (L.append xs ys) ≡ L.append (T.clauseTokensInto c xs) ys
clauseAppend [] xs ys = refl
clauseAppend (l ∷ ls) xs ys rewrite clauseAppend ls xs ys |
  literalAppend l (T.clauseTokensInto ls xs) ys = refl

bodyAppend : ∀ {n} (f : CNF.CNF n) xs ys →
  bodyInto f (L.append xs ys) ≡ L.append (bodyInto f xs) ys
bodyAppend [] xs ys = refl
bodyAppend (c ∷ cs) xs ys rewrite bodyAppend cs xs ys |
  clauseAppend c (bodyInto cs xs) ys = refl

lookupSkip : ∀ (xs ys : List Bool) k →
  Lookup.lookupBit (B.listLength xs + k) (L.append xs ys) ≡ Lookup.lookupBit k ys
lookupSkip [] ys k = refl
lookupSkip (x ∷ xs) ys k = lookupSkip xs ys k

appendAssoc : ∀ {A : Set} (xs ys zs : List A) →
  L.append (L.append xs ys) zs ≡ L.append xs (L.append ys zs)
appendAssoc [] ys zs = refl
appendAssoc (x ∷ xs) ys zs rewrite appendAssoc xs ys zs = refl

-- B.append and L.append are extensionally identical.
appendSame : ∀ {A : Set} (xs ys : List A) → B.append xs ys ≡ L.append xs ys
appendSame [] ys = refl
appendSame (x ∷ xs) ys rewrite appendSame xs ys = refl

binaryAppend : ∀ (xs ys : List P.CookSyntaxToken) →
  B.encodeTokenStream (L.append xs ys)
  ≡ L.append (B.encodeTokenStream xs) (B.encodeTokenStream ys)
binaryAppend [] ys = refl
binaryAppend (x ∷ xs) ys
  rewrite binaryAppend xs ys
        | appendSame (B.tokenBits x) (L.append (B.encodeTokenStream xs) (B.encodeTokenStream ys))
        | appendSame (B.tokenBits x) (B.encodeTokenStream xs) =
  sym (appendAssoc (B.tokenBits x) (B.encodeTokenStream xs) (B.encodeTokenStream ys))

-- Actual serialized bit at an exact body boundary. Neither side duplicates
-- the final TRUE. This is the flattened-stream receiver for arithmetic sums.
prefixBitExact : ∀ {n} (f g : CNF.CNF n) k →
  Lookup.lookupBit (3 * bodyWidth f + k) (T.cnfTokenBits (L.append f g))
  ≡ Lookup.lookupBit k (T.cnfTokenBits g)
prefixBitExact f g k
  rewrite actualTokens (L.append f g) [] | bodyCompose f g (P.formulaTrueToken ∷ [])
        | actualTokens g []
        | bodyAppend f [] (bodyInto g (P.formulaTrueToken ∷ []))
        | binaryAppend (bodyInto f []) (bodyInto g (P.formulaTrueToken ∷ []))
        = transport
  where
    prefix = B.encodeTokenStream (bodyInto f [])
    suffix = B.encodeTokenStream (bodyInto g (P.formulaTrueToken ∷ []))
    lengthExact : B.listLength prefix ≡ 3 * bodyWidth f
    lengthExact rewrite B.encodeTokenStreamLength (bodyInto f []) | bodyLength f [] |
      N.+-identityʳ (bodyWidth f) = refl
    transport : Lookup.lookupBit (3 * bodyWidth f + k) (L.append prefix suffix)
      ≡ Lookup.lookupBit k suffix
    transport rewrite sym lengthExact = lookupSkip prefix suffix k
